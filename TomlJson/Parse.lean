module

public import TomlJson.Render

/-! # Reading JSON text

`Value.parse` reads any JSON text (RFC 8259) whose data fits the model, and yields the normal
value it denotes. `Value.parseCanonical` reads canonical text only: it is `parse` followed by the
check that the text is the value's rendering, so `render` of what it returns is the text it read,
by construction.

What `parse` takes and what it does not:

* whitespace between tokens, any escape (`\/`, surrogate pairs, either case of hex digits);
* numbers: without a point or exponent an integer (any size), otherwise the nearest float;
  a float beyond binary64's range is an error, as is a number of more than `maxNumberDigits`
  digits (as Python's limit on `int` text);
* `null` as a table member's value: the member is dropped, as TOML has no null;
  `null` anywhere else is an error;
* duplicate keys, unpaired surrogates, control characters in strings, nesting deeper than
  `maxDepth` and trailing text are errors.
-/

public section

namespace TomlJson

/-- The deepest nesting of arrays and tables `Value.parse` reads. -/
def maxDepth : Nat := 1000

/-- The most digits (before and after the point) a number may have; Python's `int` limit. -/
def maxNumberDigits : Nat := 4300

namespace Parser

/-- The byte at `i`, if any. -/
@[inline] private def peek (b : ByteArray) (i : Nat) : Option UInt8 :=
  if h : i < b.size then some b[i] else none

/-- An error at byte offset `i`. -/
private def fail {α : Type} (i : Nat) (msg : String) : Except String α :=
  .error s!"at byte {i}: {msg}"

/-- The offset of the first byte at or after `i` that is not JSON whitespace. -/
private partial def skipWs (b : ByteArray) (i : Nat) : Nat :=
  match peek b i with
  | some 0x20 | some 0x09 | some 0x0A | some 0x0D => skipWs b (i + 1)
  | _ => i

/-- `acc` followed by the UTF-8 encoding of the scalar value `cp`. -/
private def pushUtf8 (acc : ByteArray) (cp : Nat) : ByteArray :=
  if cp < 0x80 then acc.push cp.toUInt8
  else if cp < 0x800 then
    (acc.push (0xC0 + cp / 64).toUInt8).push (0x80 + cp % 64).toUInt8
  else if cp < 0x10000 then
    ((acc.push (0xE0 + cp / 4096).toUInt8).push (0x80 + cp / 64 % 64).toUInt8).push
      (0x80 + cp % 64).toUInt8
  else
    (((acc.push (0xF0 + cp / 262144).toUInt8).push (0x80 + cp / 4096 % 64).toUInt8).push
      (0x80 + cp / 64 % 64).toUInt8).push (0x80 + cp % 64).toUInt8

/-- The value of a hexadecimal digit. -/
private def hexValue (c : UInt8) : Option Nat :=
  if 0x30 ≤ c && c ≤ 0x39 then some (c.toNat - 0x30)
  else if 0x61 ≤ c && c ≤ 0x66 then some (c.toNat - 0x57)
  else if 0x41 ≤ c && c ≤ 0x46 then some (c.toNat - 0x37) else none

/-- The code unit of the four hexadecimal digits at `i`. -/
private def hex4 (b : ByteArray) (i : Nat) : Except String Nat := do
  let mut n := 0
  for k in [0:4] do
    match (peek b (i + k)).bind hexValue with
    | some d => n := n * 16 + d
    | none => fail (i + k) "expected four hexadecimal digits after \\u"
  return n

/-- A string's contents from `i` (just past its opening quote) to its closing quote; the offset
past that quote. -/
private partial def stringBody (b : ByteArray) (i : Nat) (acc : ByteArray) :
    Except String (String × Nat) :=
  match peek b i with
  | none => fail i "unterminated string"
  | some 0x22 =>
    match String.fromUTF8? acc with
    | some s => .ok (s, i + 1)
    | none => fail i "invalid UTF-8 in string"
  | some 0x5C =>
    let simple (byte : UInt8) := stringBody b (i + 2) (acc.push byte)
    match peek b (i + 1) with
    | some 0x22 => simple 0x22
    | some 0x5C => simple 0x5C
    | some 0x2F => simple 0x2F
    | some 0x62 => simple 0x08
    | some 0x66 => simple 0x0C
    | some 0x6E => simple 0x0A
    | some 0x72 => simple 0x0D
    | some 0x74 => simple 0x09
    | some 0x75 => do
      let u ← hex4 b (i + 2)
      if 0xD800 ≤ u && u < 0xDC00 then
        if peek b (i + 6) == some 0x5C && peek b (i + 7) == some 0x75 then
          let low ← hex4 b (i + 8)
          if 0xDC00 ≤ low && low < 0xE000 then
            stringBody b (i + 12) (pushUtf8 acc (0x10000 + (u - 0xD800) * 0x400 + (low - 0xDC00)))
          else fail (i + 6) "a high surrogate must be followed by a low one"
        else fail i "unpaired surrogate (a Lean string holds only scalar values)"
      else if 0xDC00 ≤ u && u < 0xE000 then
        fail i "unpaired surrogate (a Lean string holds only scalar values)"
      else stringBody b (i + 6) (pushUtf8 acc u)
    | _ => fail i "invalid escape"
  | some c =>
    if c < 0x20 then fail i "control character in string (it must be escaped)"
    else stringBody b (i + 1) (acc.push c)

/-- A run of decimal digits from `i`: their value (accumulated past `acc`, up to
`maxNumberDigits` digits in all), the count of digits (past `count`) and the offset past them. -/
private partial def digits (b : ByteArray) (i : Nat) (acc count : Nat) : Nat × Nat × Nat :=
  match peek b i with
  | some c =>
    if 0x30 ≤ c && c ≤ 0x39 then
      let acc := if count < maxNumberDigits then acc * 10 + (c.toNat - 0x30) else acc
      digits b (i + 1) acc (count + 1)
    else (acc, count, i)
  | none => (acc, count, i)

/-- The value of a run of decimal digits from `i`, saturating at `10^10` (an exponent that large
decides the result as its exact value would), and the offset past them. -/
private partial def exponentDigits (b : ByteArray) (i : Nat) (acc : Nat) : Nat × Nat :=
  match peek b i with
  | some c =>
    if 0x30 ≤ c && c ≤ 0x39 then exponentDigits b (i + 1) (min (acc * 10 + (c.toNat - 0x30)) (10 ^ 10))
    else (acc, i)
  | none => (acc, i)

/-- Whether the byte at `i` is a decimal digit. -/
private def digitAt (b : ByteArray) (i : Nat) : Bool :=
  match peek b i with
  | some c => 0x30 ≤ c && c ≤ 0x39
  | none => false

/-- The number at `i` (RFC 8259 grammar), and the offset past it. -/
private def number (b : ByteArray) (start : Nat) : Except String (Value × Nat) := do
  let negative := peek b start == some 0x2D
  let i := if negative then start + 1 else start
  if !digitAt b i then fail i "expected a digit"
  -- The integer part: `0`, or a digit from 1 to 9 and more digits.
  let (m, count, i) :=
    if peek b i == some 0x30 then (0, 1, i + 1) else digits b i 0 0
  if digitAt b i then fail i "a number does not start with 0 and then another digit"
  -- The fraction.
  let (m, count, fraction, i) ←
    if peek b i == some 0x2E then
      if !digitAt b (i + 1) then fail (i + 1) "expected a digit after the point"
      let (m', count', j) := digits b (i + 1) m count
      pure (m', count', count' - count, j)
    else pure (m, count, 0, i)
  if count > maxNumberDigits then fail start s!"a number has more than {maxNumberDigits} digits"
  -- The exponent.
  let (exponent, hasExponent, i) ← do
    match peek b i with
    | some 0x65 | some 0x45 =>
      let (minus, j) :=
        match peek b (i + 1) with
        | some 0x2D => (true, i + 2)
        | some 0x2B => (false, i + 2)
        | _ => (false, i + 1)
      if !digitAt b j then fail j "expected a digit in the exponent"
      let (e, k) := exponentDigits b j 0
      let e : Int := e
      pure (if minus then -e else e, true, k)
    | _ => pure (0, false, i)
  -- A point or an exponent makes a float; the grammar gives a point at least one digit.
  if !hasExponent && fraction == 0 then
    return (.integer (if negative then -(m : Int) else m), i)
  match FloatText.ofDecimal? negative m (exponent - fraction) with
  | some x => return (.float x, i)
  | none => fail start "a float beyond the range of binary64"

/-- The literal `word` at `i`, as its bytes. -/
private def literal (b : ByteArray) (i : Nat) (word : String) : Bool :=
  let w := word.toUTF8
  (List.range w.size).all fun k => peek b (i + k) == w[k]?

mutual

/-- The value at `i` (after whitespace), `none` for `null`, and the offset past it. -/
private partial def value (b : ByteArray) (i : Nat) (depth : Nat) :
    Except String (Option Value × Nat) :=
  match peek b i with
  | none => fail i "expected a value, found the end of the text"
  | some 0x22 => do
    let (s, j) ← stringBody b (i + 1) .empty
    return (some (.string s), j)
  | some 0x5B => if depth ≥ maxDepth then fail i "nested too deeply" else array b (i + 1) (depth + 1)
  | some 0x7B => if depth ≥ maxDepth then fail i "nested too deeply" else table b (i + 1) (depth + 1)
  | some 0x74 => if literal b i "true" then .ok (some (.boolean true), i + 4) else fail i "expected true"
  | some 0x66 =>
    if literal b i "false" then .ok (some (.boolean false), i + 5) else fail i "expected false"
  | some 0x6E => if literal b i "null" then .ok (none, i + 4) else fail i "expected null"
  | some c =>
    if c == 0x2D || (0x30 ≤ c && c ≤ 0x39) then do
      let (v, j) ← number b i
      return (some v, j)
    else fail i "expected a value"

/-- An array's items from `i` (just past `[`) to `]`; the offset past it. -/
private partial def array (b : ByteArray) (i : Nat) (depth : Nat) :
    Except String (Option Value × Nat) := do
  let i := skipWs b i
  if peek b i == some 0x5D then return (some (.array #[]), i + 1)
  let mut items := #[]
  let mut i := i
  repeat
    let start := skipWs b i
    let (item, j) ← value b start depth
    match item with
    | some v => items := items.push v
    | none => fail start "null has no TOML counterpart (only a table member may be null: it is dropped)"
    let j := skipWs b j
    match peek b j with
    | some 0x2C => i := j + 1
    | some 0x5D => return (some (.array items), j + 1)
    | _ => fail j "expected , or ] in an array"
  fail i "unreachable"

/-- A table's members from `i` (just past `{`) to `}`; the offset past it. -/
private partial def table (b : ByteArray) (i : Nat) (depth : Nat) :
    Except String (Option Value × Nat) := do
  let i := skipWs b i
  if peek b i == some 0x7D then return (some (.table #[]), i + 1)
  let mut members : Array (String × Option Value × Nat) := #[]
  let mut i := i
  repeat
    let start := skipWs b i
    if peek b start != some 0x22 then fail start "expected a string key"
    let (key, j) ← stringBody b (start + 1) .empty
    let j := skipWs b j
    if peek b j != some 0x3A then fail j "expected : after a key"
    let (item, j) ← value b (skipWs b (j + 1)) depth
    members := members.push (key, item, start)
    let j := skipWs b j
    match peek b j with
    | some 0x2C => i := j + 1
    | some 0x7D =>
      -- Sorted by key, then by place: a repeated key's later members follow its first.
      let sorted := members.qsort fun (k, _, i) (l, _, j) => k < l || (k == l && i < j)
      -- Report the repeat that comes first in the text.
      let mut earliest? : Option (String × Nat) := none
      for k in [1:sorted.size] do
        if sorted[k - 1]!.1 == sorted[k]!.1 then
          let place := sorted[k]!.2.2
          if earliest?.all (place < ·.2) then earliest? := some (sorted[k]!.1, place)
      if let some (key, place) := earliest? then
        fail place s!"duplicate key {pushString "" key}"
      let kept := sorted.filterMap fun (k, v, _) => v.map (k, ·)
      return (some (.table kept), j + 1)
    | _ => fail j "expected , or } in a table"
  fail i "unreachable"

end

end Parser

namespace Value

/-- The value a JSON text denotes, normalized (see the module docstring for what is accepted). -/
def parse (s : String) : Except String Value := do
  let b := s.toUTF8
  let i := Parser.skipWs b 0
  let (v, j) ← Parser.value b i 0
  let j := Parser.skipWs b j
  if j < b.size then .error s!"at byte {j}: trailing text after the value"
  match v with
  | some v => return v
  | none => .error s!"at byte {i}: null has no TOML counterpart"

/-- The first offset, in bytes, where two texts differ, with a few characters of each from there. -/
private def firstDifference (a b : String) : Nat × String × String := Id.run do
  let mut offset := 0
  let mut as := a.toList
  let mut bs := b.toList
  repeat
    match as, bs with
    | x :: xs, y :: ys =>
      if x == y then
        offset := offset + x.utf8Size
        as := xs
        bs := ys
      else break
    | _, _ => break
  return (offset, String.ofList (as.take 16), String.ofList (bs.take 16))

/-- The value of a canonical text: `parse`, then the check that the text is the value's
rendering. So `(parseCanonical s).map render = .ok s` whenever it succeeds. -/
def parseCanonical (s : String) : Except String Value := do
  let v ← parse s
  let r := v.render
  if r == s then return v
  let (offset, canon, given) := firstDifference r s
  .error s!"at byte {offset}: not canonical: the canonical text continues `{canon}`, this one `{given}`"

/-- The values of JSON Lines text: one value a line; a line feed may be preceded by a carriage
return, and blank lines (JSON whitespace only) are skipped. -/
def parseLines (s : String) : Except String (Array Value) := do
  let mut out := #[]
  let mut number := 0
  for line in s.splitOn "\n" do
    number := number + 1
    let line := if line.endsWith "\r" then String.ofList line.toList.dropLast else line
    if line.all (fun c => c == ' ' || c == '\t' || c == '\r') then continue
    match parse line with
    | .ok v => out := out.push v
    | .error e => throw s!"line {number}, {e}"
  return out

/-- The values of canonical JSON Lines text: exactly `renderLines` of the values. -/
def parseLinesCanonical (s : String) : Except String (Array Value) := do
  if s.isEmpty then return #[]
  if !s.endsWith "\n" then throw "canonical JSON Lines text ends with a line feed"
  let lines := (s.splitOn "\n").dropLast
  let mut out := #[]
  let mut number := 0
  for line in lines do
    number := number + 1
    match parseCanonical line with
    | .ok v => out := out.push v
    | .error e => throw s!"line {number}, {e}"
  return out

end Value

end TomlJson
