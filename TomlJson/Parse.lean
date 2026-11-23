module

public import TomlJson.Render

/-! # Reading canonical text

`Value.parse` reads canonical text and nothing else: it succeeds on `s` exactly when
`s = render v` for a valid value `v` (within the limits below), and returns that `v`. Any other
text, however close (whitespace, `1.00`, `\/`, keys out of order), is an error at its byte offset,
naming the canonical spelling where there is one.

Limits, which bound the reader's work: at most `maxNumberDigits` digits in a number, nesting at
most `maxDepth` deep.
-/

public section

namespace TomlJson

/-- The deepest nesting of arrays and tables `Value.parse` reads. -/
def maxDepth : Nat := 1000

/-- The most digits a number may have (CPython's limit for `int` text). -/
def maxNumberDigits : Nat := 4300

namespace Parser

/-- The byte at `i`, if any. -/
@[inline] private def peek (b : ByteArray) (i : Nat) : Option UInt8 :=
  if h : i < b.size then some b[i] else none

/-- An error at byte offset `i`. -/
private def fail {α : Type} (i : Nat) (msg : String) : Except String α :=
  .error s!"at byte {i}: {msg}"

/-- The value of a hexadecimal digit (either case). -/
private def hexValue (c : Option UInt8) : Option Nat :=
  match c with
  | some c =>
    if 0x30 ≤ c && c ≤ 0x39 then some (c.toNat - 0x30)
    else if 0x61 ≤ c && c ≤ 0x66 then some (c.toNat - 0x57)
    else if 0x41 ≤ c && c ≤ 0x46 then some (c.toNat - 0x37) else none
  | none => none

/-- The code unit of the four hexadecimal digits at `i`. -/
private def hex4 (b : ByteArray) (i : Nat) : Option Nat := do
  let d (k : Nat) := hexValue (peek b (i + k))
  return (← d 0) * 4096 + (← d 1) * 256 + (← d 2) * 16 + (← d 3)

/-- The text of bytes `i` to `j` (ASCII here). -/
private def textOf (b : ByteArray) (i j : Nat) : String :=
  (String.fromUTF8? (b.extract i j)).getD "?"

/-- A string's contents from `i` (just past its opening quote) to its closing quote, and the
offset past that quote. Only the canonical escapes are taken (see `pushChar`). -/
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
    | some 0x62 => simple 0x08
    | some 0x74 => simple 0x09
    | some 0x6E => simple 0x0A
    | some 0x66 => simple 0x0C
    | some 0x72 => simple 0x0D
    | some 0x2F => fail i "write /, not \\/"
    | some 0x75 =>
      match hex4 b (i + 2) with
      | none => fail i "expected four hexadecimal digits after \\u"
      | some u =>
        let written := textOf b i (i + 6)
        if 0xD800 ≤ u && u < 0xDC00 then
          let low := if peek b (i + 6) == some 0x5C && peek b (i + 7) == some 0x75 then hex4 b (i + 8) else none
          match low with
          | some low =>
            if 0xDC00 ≤ low && low < 0xE000 then
              let c := Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (low - 0xDC00))
              fail i s!"write {String.singleton c}, not the surrogate pair {written}{textOf b (i + 6) (i + 12)}"
            else fail i s!"{written} is a lone surrogate, not a character"
          | none => fail i s!"{written} is a lone surrogate, not a character"
        else if 0xDC00 ≤ u && u < 0xE000 then fail i s!"{written} is a lone surrogate, not a character"
        else
          -- Only a control character without a two-character escape is written `\u00xx`.
          let canonical := pushChar "" (Char.ofNat u)
          if canonical == written then stringBody b (i + 6) (acc.push u.toUInt8)
          else fail i s!"write {canonical}, not {written}"
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

/-- The number at `start`, which must be written canonically, and the offset past it. A number
in any other spelling, leading zeros included, is an error that names its canonical text. -/
private def number (b : ByteArray) (start : Nat) : Except String (Value × Nat) := do
  let negative := peek b start == some 0x2D
  let i := if negative then start + 1 else start
  if !digitAt b i then fail i "expected a digit"
  let (m, count, i) := digits b i 0 0
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
      pure (if minus then -(e : Int) else e, true, k)
    | _ => pure (0, false, i)
  let token := textOf b start i
  if !hasExponent && fraction == 0 then
    let n : Int := if negative then -(m : Int) else m
    let canonical := toString n
    if token == canonical then return (.integer n, i)
    fail start s!"not the canonical text of this integer: write {canonical}"
  match FloatText.ofDecimal? negative m (exponent - fraction) with
  | none => fail start "a float beyond the range of binary64"
  | some x =>
    let canonical := floatText x
    if token == canonical then return (.float x, i)
    fail start s!"not the canonical text of this float: write {canonical}"

/-- Whether the bytes of `word` are at `i`. -/
private def literal (b : ByteArray) (i : Nat) (word : String) : Bool :=
  let w := word.toUTF8
  (List.range w.size).all fun k => peek b (i + k) == w[k]?

mutual

/-- The value at `i`, and the offset past it. -/
private partial def value (b : ByteArray) (i : Nat) (depth : Nat) : Except String (Value × Nat) :=
  match peek b i with
  | none => fail i "expected a value, found the end of the text"
  | some 0x22 => do
    let (s, j) ← stringBody b (i + 1) .empty
    return (.string s, j)
  | some 0x5B => if depth ≥ maxDepth then fail i "nested too deeply" else array b (i + 1) (depth + 1)
  | some 0x7B => if depth ≥ maxDepth then fail i "nested too deeply" else table b (i + 1) (depth + 1)
  | some 0x6E => if literal b i "null" then .ok (.null, i + 4) else fail i "expected null"
  | some 0x74 => if literal b i "true" then .ok (.boolean true, i + 4) else fail i "expected true"
  | some 0x66 => if literal b i "false" then .ok (.boolean false, i + 5) else fail i "expected false"
  | some c =>
    if c == 0x2D || (0x30 ≤ c && c ≤ 0x39) then number b i
    else if c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D then
      fail i "canonical text has no whitespace"
    else fail i "expected a value"

/-- An array's items from `i` (just past `[`) to `]`, and the offset past it. -/
private partial def array (b : ByteArray) (i : Nat) (depth : Nat) : Except String (Value × Nat) := do
  if peek b i == some 0x5D then return (.array #[], i + 1)
  let mut items := #[]
  let mut i := i
  repeat
    let (item, j) ← value b i depth
    items := items.push item
    match peek b j with
    | some 0x2C => i := j + 1
    | some 0x5D => return (.array items, j + 1)
    | _ => fail j "expected , or ] (canonical text has no whitespace)"
  fail i "unreachable"

/-- A table's members from `i` (just past `{`) to `}`, keys strictly increasing, and the offset
past it. -/
private partial def table (b : ByteArray) (i : Nat) (depth : Nat) : Except String (Value × Nat) := do
  if peek b i == some 0x7D then return (.table #[], i + 1)
  let mut members : Array (String × Value) := #[]
  let mut i := i
  repeat
    if peek b i != some 0x22 then fail i "expected a string key"
    let (key, j) ← stringBody b (i + 1) .empty
    if let some (previous, _) := members.back? then
      if key == previous then fail i s!"duplicate key {pushString "" key}"
      if !(previous < key) then
        fail i s!"keys must increase: {pushString "" key} comes before {pushString "" previous}"
    if peek b j != some 0x3A then fail j "expected : after a key (canonical text has no whitespace)"
    let (item, j) ← value b (j + 1) depth
    members := members.push (key, item)
    match peek b j with
    | some 0x2C => i := j + 1
    | some 0x7D => return (.table members, j + 1)
    | _ => fail j "expected , or } (canonical text has no whitespace)"
  fail i "unreachable"

end

end Parser

namespace Value

/-- The valid value whose text is `s`, if `s` is canonical (see the module docstring). -/
def parse (s : String) : Except String Value := do
  let b := s.toUTF8
  let (v, j) ← Parser.value b 0 0
  if j < b.size then .error s!"at byte {j}: text after the value (canonical text has no whitespace)"
  return v

/-- The values of canonical JSON Lines text: exactly `renderLines` of valid values, each line one
canonical text and a line feed. An error names the first line that is not. -/
def parseLines (s : String) : Except String (Array Value) := do
  let parts := s.splitOn "\n"
  let mut out := #[]
  let mut number := 0
  for line in parts, k in [0:parts.length] do
    let last := k + 1 == parts.length
    -- after the final line feed, nothing
    if last && line.isEmpty then break
    number := number + 1
    match parse line with
    | .ok v => out := out.push v
    | .error e => throw s!"line {number}, {e}"
    if last then throw s!"line {number}: no line feed at its end"
  return out

end Value

end TomlJson
