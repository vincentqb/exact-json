module

public import TomlJson.Render

/-! # Reading canonical text

`Value.parse` reads canonical text and nothing else: it succeeds on `s` exactly when
`s = render v` for a valid value `v`, and returns that `v`. Any other text, however close
(whitespace, `1.00`, `\/`, keys out of order), is an error at its character offset, naming the
canonical spelling where there is one.

The reader works on the text's characters, by structural recursion: on the characters for
strings and numbers, and on a fuel of twice the text's length for nested arrays and tables, which
always suffices. Its result is checked once more at the end (valid, and rendered back to the text
it was read from), so that what it returns is canonical by construction.
-/

@[expose] public section

namespace TomlJson

namespace Parser

/-- An error at character offset `total - rest.length`. -/
def fail {α : Type} (total : Nat) (rest : List Char) (msg : String) : Except String α :=
  .error s!"at character {total - rest.length}: {msg}"

/-- The value of a hexadecimal digit (either case). -/
def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

/-- The code unit of four hexadecimal digits. -/
def hex4 (a b c d : Char) : Option Nat := do
  return (← hexValue a) * 4096 + (← hexValue b) * 256 + (← hexValue c) * 16 + (← hexValue d)

/-- A string's contents from just past its opening quote to its closing quote, and the rest after
that quote. Only the canonical escapes are taken (see `pushChar`). -/
def string (total : Nat) : List Char → String → Except String (String × List Char)
  | [], _ => .error s!"at character {total}: unterminated string"
  | '"' :: rest, acc => .ok (acc, rest)
  | '\\' :: rest, acc =>
    match rest with
    | '"' :: r => string total r (acc.push '"')
    | '\\' :: r => string total r (acc.push '\\')
    | 'b' :: r => string total r (acc.push '\x08')
    | 't' :: r => string total r (acc.push '\t')
    | 'n' :: r => string total r (acc.push '\n')
    | 'f' :: r => string total r (acc.push '\x0c')
    | 'r' :: r => string total r (acc.push '\r')
    | '/' :: _ => fail total ('\\' :: rest) "write /, not \\/"
    | 'u' :: a :: b :: c :: d :: r =>
      let written := String.ofList ['\\', 'u', a, b, c, d]
      match hex4 a b c d with
      | none => fail total ('\\' :: rest) "expected four hexadecimal digits after \\u"
      | some u =>
        if 0xD800 ≤ u && u < 0xE000 then
          match r with
          | '\\' :: 'u' :: e :: f :: g :: h :: _ =>
            match hex4 e f g h with
            | some low =>
              if u < 0xDC00 && 0xDC00 ≤ low && low < 0xE000 then
                let char := Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (low - 0xDC00))
                fail total ('\\' :: rest)
                  s!"write {String.singleton char}, not the surrogate pair {written}{String.ofList ['\\', 'u', e, f, g, h]}"
              else fail total ('\\' :: rest) s!"{written} is a lone surrogate, not a character"
            | none => fail total ('\\' :: rest) s!"{written} is a lone surrogate, not a character"
          | _ => fail total ('\\' :: rest) s!"{written} is a lone surrogate, not a character"
        else
          -- Only a control character without a two-character escape is written `\u00xx`.
          let char := Char.ofNat u
          let canonical := pushChar "" char
          if canonical == written then string total r (acc.push char)
          else fail total ('\\' :: rest) s!"write {canonical}, not {written}"
    | _ => fail total ('\\' :: rest) "invalid escape"
  | c :: rest, acc =>
    if c.val < 0x20 then fail total (c :: rest) "control character in string (it must be escaped)"
    else string total rest (acc.push c)

/-- The value of the decimal digits at the front, past `acc`, and the rest. -/
def digits : List Char → Nat → Nat × List Char
  | c :: rest, acc => if c.isDigit then digits rest (acc * 10 + (c.toNat - 48)) else (acc, c :: rest)
  | [], acc => (acc, [])

/-- The number at the front (JSON's grammar), which must be written canonically, and the rest. A
number in any other spelling, leading zeros included, is an error that names its canonical text. -/
def number (total : Nat) (input : List Char) : Except String (Value × List Char) := do
  let (negative, afterSign) := match input with
    | '-' :: rest => (true, rest)
    | rest => (false, rest)
  let startsWithDigit := match afterSign with
    | c :: _ => c.isDigit
    | [] => false
  if !startsWithDigit then fail total afterSign "expected a digit"
  let (whole, afterWhole) := digits afterSign 0
  -- The fraction: a point and at least one digit.
  let (m, fraction, afterFraction) ← match afterWhole with
    | '.' :: rest =>
      let (m, after) := digits rest whole
      let count := rest.length - after.length
      if count == 0 then fail total rest "expected a digit after the point"
      else pure (m, count, after)
    | rest => pure (whole, 0, rest)
  -- The exponent: `e` or `E`, a sign perhaps, and at least one digit.
  let (exponent, hasExponent, rest) ← match afterFraction with
    | e :: rest =>
      if e == 'e' || e == 'E' then
        let (minus, digitsAt) := match rest with
          | '-' :: r => (true, r)
          | '+' :: r => (false, r)
          | r => (false, r)
        let (value, after) := digits digitsAt 0
        if digitsAt.length == after.length then fail total digitsAt "expected a digit in the exponent"
        else pure ((if minus then -(value : Int) else value), true, after)
      else pure (0, false, e :: rest)
    | [] => pure (0, false, [])
  let token := String.ofList (input.take (input.length - rest.length))
  if !hasExponent && fraction == 0 then
    let n : Int := if negative then -(m : Int) else m
    let canonical := toString n
    if token == canonical then return (.integer n, rest)
    fail total input s!"not the canonical text of this integer: write {canonical}"
  match FloatText.ofDecimal? negative m (exponent - fraction) with
  | none => fail total input "a float beyond the range of binary64"
  | some x =>
    let canonical := floatText x
    if token == canonical then return (.float x, rest)
    fail total input s!"not the canonical text of this float: write {canonical}"

/-- Whether `c` is JSON whitespace. -/
def isWhitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

mutual

/-- The value at the front, and the rest. -/
def value (total : Nat) : Nat → List Char → Except String (Value × List Char)
  | 0, input => fail total input "nested deeper than the reader's fuel"
  | fuel + 1, input =>
    match input with
    | [] => fail total [] "expected a value, found the end of the text"
    | '"' :: rest => do
      let (s, after) ← string total rest ""
      return (.string s, after)
    | '[' :: ']' :: rest => .ok (.array #[], rest)
    | '[' :: rest => items total fuel rest #[]
    | '{' :: '}' :: rest => .ok (.table #[], rest)
    | '{' :: rest => members total fuel rest #[]
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.boolean true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.boolean false, rest)
    | c :: rest =>
      if c == '-' || c.isDigit then number total (c :: rest)
      else if isWhitespace c then fail total (c :: rest) "canonical text has no whitespace"
      else fail total (c :: rest) "expected a value"

/-- An array's items from just past `[` or a comma, `acc` read so far, and the rest after `]`. -/
def items (total : Nat) : Nat → List Char → Array Value → Except String (Value × List Char)
  | 0, input, _ => fail total input "nested deeper than the reader's fuel"
  | fuel + 1, input, acc => do
    let (item, after) ← value total fuel input
    match after with
    | ',' :: rest => items total fuel rest (acc.push item)
    | ']' :: rest => return (.array (acc.push item), rest)
    | rest => fail total rest "expected , or ] (canonical text has no whitespace)"

/-- A table's members from just past `{` or a comma, `acc` read so far, keys strictly increasing,
and the rest after `}`. -/
def members (total : Nat) : Nat → List Char → Array (String × Value) →
    Except String (Value × List Char)
  | 0, input, _ => fail total input "nested deeper than the reader's fuel"
  | fuel + 1, input, acc =>
    match input with
    | '"' :: rest => do
      let (key, afterKey) ← string total rest ""
      if let some (previous, _) := acc.back? then
        if key == previous then fail total input s!"duplicate key {pushString "" key}"
        if !decide (previous < key) then
          fail total input s!"keys must increase: {pushString "" key} comes before {pushString "" previous}"
      match afterKey with
      | ':' :: rest => do
        let (item, after) ← value total fuel rest
        match after with
        | ',' :: more => members total fuel more (acc.push (key, item))
        | '}' :: more => return (.table (acc.push (key, item)), more)
        | more => fail total more "expected , or } (canonical text has no whitespace)"
      | more => fail total more "expected : after a key (canonical text has no whitespace)"
    | more => fail total more "expected a string key"

end

/-- The value a text holds by the reader's rules alone, before the final check. -/
def run (s : String) : Except String Value := do
  let input := s.toList
  let total := input.length
  let (v, rest) ← value total (2 * total + 2) input
  if rest.isEmpty then return v
  fail total rest "text after the value (canonical text has no whitespace)"

end Parser

namespace Value

/-- The valid value whose canonical text is `s`, if `s` is one (see the module docstring). -/
def parse (s : String) : Except String Value :=
  match Parser.run s with
  | .error e => .error e
  | .ok v =>
    if v.isValid && v.render == s then .ok v
    else .error "read a value whose canonical text differs (this is a bug in the reader)"

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
