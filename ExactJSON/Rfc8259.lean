module

public import ExactJSON.Value

/-!
# JSON as RFC 8259 writes it, and the value it holds

`Rfc8259.read? s` is the value that the JSON text `s` holds, or `none` when `s` is not read. It
follows RFC 8259's grammar exactly (§2 to §7): whitespace only where the grammar has `ws`, the
literals `true`, `false` and `null`, numbers without leading zeros, strings with the RFC's escapes,
arrays and objects. What a JSON text holds is a value of this format, as follows.

* A number is an integer when it has neither a fraction nor an exponent, as Python's `json`
  reads it, and otherwise the float nearest it, which must be finite (§6 lets a reader limit the
  range of numbers).
* A string is its characters, a surrogate pair escaped as `\uD83D\uDE00` being one character
  (§8.2). A surrogate escaped alone is not read: a `String` holds characters only.
* An object, which is unordered (§4), is a table of its members sorted by key. An object in which
  a key repeats is not read (§4 leaves its meaning to the reader).

`Rfc8259.read s` also says why a text is not read, and where it stops.

The reader is written for the reader of this file, not for speed, but it is linear in the text
except for the arithmetic on a number's digits. Fuel bounds the nesting it reads: twice the text's
size in bytes and two more, which no text uses up, since each unit spent reads a character.
-/

@[expose] public section

namespace ExactJSON

namespace Rfc8259

/-- What reading part of a text gives: a result and the rest of the text after it, or why the
text is not read and the rest of the text from where reading stops. -/
abbrev Reading (α : Type) := Except (String × List Char) (α × List Char)

/-- Whether `c` is whitespace (`ws`, §2): a space, a horizontal tab, a line feed or a carriage
return. -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

/-- The text past the whitespace at its front. -/
def skipWs : List Char → List Char
  | c :: rest => if isWs c then skipWs rest else c :: rest
  | [] => []

/-- Whether `c` is one of the characters numbers are written in (§6): a digit, `-`, `+`, `.`, `e`
or `E`. In a JSON text a number is a longest run of them, since what may come before or after a
number (whitespace, `[`, `,`, `:`, `]`, `}`) is none of them. -/
def isNumberChar (c : Char) : Bool :=
  c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

/-- The natural number that the decimal digits `ds` stand for. -/
def digitsValue (ds : List Char) : Nat := Nat.ofDigitChars 10 ds 0

/-- `digitsValue ds`, or `bound` if that is less. -/
def digitsValueUpTo (bound : Nat) (ds : List Char) : Nat :=
  ds.foldl (fun n d => min (10 * n + (d.toNat - 48)) bound) 0

/-- The float nearest `(-1)^negative × m × 10^q`, rounding to nearest with ties to even as
`Float.ofScientific` does, or `none` when that is an infinity. A decimal exponent far out of range
decides without its power of ten being computed: `10^(n+q-1) ≤ m × 10^q < 10^(n+q)` for the `n`
digits of `m`, so beyond `10^309` the float is infinite, and below `10^-324` it is zero. -/
def floatOf? (negative : Bool) (m : Nat) (q : Int) : Option Float :=
  let magnitude : Option Float :=
    if m = 0 then some 0.0
    else
      let n : Int := (Nat.toDigits 10 m).length
      if n + q > 309 then none
      else if n + q < -324 then some 0.0
      else some (Float.ofScientific m (q < 0) q.natAbs)
  match magnitude.map fun f => if negative then -f else f with
  | some x => if finiteFloat x then some x else none
  | none => none

/-- The value of the number written as all of `token` (§6): `[ minus ] int [ frac ] [ exp ]`, where
`int` is `0` or digits not starting with `0`, `frac` is `.` and digits, and `exp` is `e` or `E`, a
sign or none, and digits. It is an integer when there is neither a fraction nor an exponent, and
otherwise the float nearest it, if that is finite. An exponent is counted only up to the token's
length and 400: one that large already makes the float infinite or zero (see `floatOf?`). -/
def numberValue (token : List Char) : Except String Value :=
  let (negative, t) : Bool × List Char := match token with
    | '-' :: t => (true, t)
    | t => (false, t)
  let (whole, t) := t.span Char.isDigit
  if whole.isEmpty then .error "expected a digit"
  else if whole.head? == some '0' && whole.length > 1 then .error "a number starts with no 0 but 0 itself"
  else
    let fraction : Except String (Option (List Char) × List Char) := match t with
      | '.' :: t =>
        let (ds, t) := t.span Char.isDigit
        if ds.isEmpty then .error "expected a digit after the point" else .ok (some ds, t)
      | t => .ok (none, t)
    match fraction with
    | .error e => .error e
    | .ok (fraction, t) =>
      let exponent : Except String (Option Int × List Char) := match t with
        | e :: t =>
          if e == 'e' || e == 'E' then
            let (minus, t) : Bool × List Char := match t with
              | '-' :: t => (true, t)
              | '+' :: t => (false, t)
              | t => (false, t)
            let (ds, t) := t.span Char.isDigit
            let size := digitsValueUpTo (token.length + 400) ds
            if ds.isEmpty then .error "expected a digit in the exponent"
            else .ok (some (if minus then -(size : Int) else size), t)
          else .ok (none, e :: t)
        | [] => .ok (none, [])
      match exponent with
      | .error e => .error e
      | .ok (_, _ :: _) => .error "not a number"
      | .ok (exponent, []) =>
        let m := digitsValue (whole ++ fraction.getD [])
        match fraction, exponent with
        | none, none => .ok (.integer (if negative then -(m : Int) else m))
        | _, _ =>
          match floatOf? negative m (exponent.getD 0 - ((fraction.getD []).length : Int)) with
          | some x => .ok (.float x)
          | none => .error "a float beyond the range of binary64"

/-- The value of a hexadecimal digit, either case. -/
def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

/-- The code unit that four hexadecimal digits write. -/
def hex4? (a b c d : Char) : Option Nat := do
  return (← hexValue? a) * 4096 + (← hexValue? b) * 256 + (← hexValue? c) * 16 + (← hexValue? d)

/-- The character that a backslash and `e` write, for the two-character escapes (§7). -/
def unescape? : Char → Option Char
  | '"' => some '"'
  | '\\' => some '\\'
  | '/' => some '/'
  | 'b' => some '\x08'
  | 'f' => some '\x0c'
  | 'n' => some '\n'
  | 'r' => some '\r'
  | 't' => some '\t'
  | _ => none

/-- A string's characters from just past its opening quote (§7), with `acc` the characters read
before them, last first; and the rest past its closing quote. A character below U+0020 must be
escaped. `\uXXXX` writes the character U+XXXX; a high surrogate so written must be followed by a
low one, and the two write one character (§8.2). -/
def chars : List Char → List Char → Reading (List Char)
  | [], _ => .error ("a string is not closed", [])
  | '"' :: rest, acc => .ok (acc.reverse, rest)
  | '\\' :: 'u' :: a :: b :: c :: d :: rest, acc =>
    match hex4? a b c d with
    | none => .error ("expected four hexadecimal digits after \\u", '\\' :: 'u' :: a :: b :: c :: d :: rest)
    | some u =>
      if u < 0xD800 || 0xE000 ≤ u then chars rest (Char.ofNat u :: acc)
      else if u < 0xDC00 then
        match rest with
        | '\\' :: 'u' :: e :: f :: g :: h :: after =>
          match hex4? e f g h with
          | some low =>
            if 0xDC00 ≤ low && low < 0xE000 then
              chars after (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (low - 0xDC00)) :: acc)
            else .error ("a high surrogate not followed by a low one", '\\' :: 'u' :: a :: b :: c :: d :: rest)
          | none => .error ("a high surrogate not followed by a low one", '\\' :: 'u' :: a :: b :: c :: d :: rest)
        | _ => .error ("a high surrogate not followed by a low one", '\\' :: 'u' :: a :: b :: c :: d :: rest)
      else .error ("a low surrogate not after a high one", '\\' :: 'u' :: a :: b :: c :: d :: rest)
  | '\\' :: e :: rest, acc =>
    match unescape? e with
    | some c => chars rest (c :: acc)
    | none => .error ("not an escape", '\\' :: e :: rest)
  | c :: rest, acc =>
    if c.val < 0x20 then .error ("a character below U+0020 must be escaped", c :: rest)
    else chars rest (c :: acc)

/-- Whether no two neighbours in `members` have the same key. -/
def neighboursDistinct : List (String × Value) → Bool
  | a :: b :: rest => a.1 != b.1 && neighboursDistinct (b :: rest)
  | _ => true

/-- The table of an object's members, which is unordered (§4): the members sorted by key, or the
key that repeats. -/
def table (members : List (String × Value)) : Except String Value :=
  let sorted := members.mergeSort fun a b => decide (a.1 ≤ b.1)
  if neighboursDistinct sorted then .ok (.table sorted.toArray)
  else .error "a key repeats"

mutual

/-- The value at the front of `input`, which starts past any whitespace (§3), and the rest after
it. -/
def value : Nat → List Char → Reading Value
  | 0, input => .error ("nested deeper than the fuel", input)
  | fuel + 1, input =>
    match input with
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok (.null, rest)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.boolean true, rest)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.boolean false, rest)
    | '"' :: rest =>
      match chars rest [] with
      | .ok (cs, after) => .ok (.string (String.ofList cs), after)
      | .error e => .error e
    | '[' :: rest =>
      match skipWs rest with
      | ']' :: after => .ok (.array #[], after)
      | first => elements fuel first #[]
    | '{' :: rest =>
      match skipWs rest with
      | '}' :: after => .ok (.table #[], after)
      | first => members fuel first #[]
    | input =>
      let (token, rest) := input.span isNumberChar
      if token.isEmpty then .error ("expected a value", input)
      else
        match numberValue token with
        | .ok v => .ok (v, rest)
        | .error e => .error (e, input)

/-- An array's elements (§5) from the next one, `acc` read so far, and the rest after its `]`. -/
def elements : Nat → List Char → Array Value → Reading Value
  | 0, input, _ => .error ("nested deeper than the fuel", input)
  | fuel + 1, input, acc =>
    match value fuel input with
    | .ok (v, rest) =>
      match skipWs rest with
      | ',' :: after => elements fuel (skipWs after) (acc.push v)
      | ']' :: after => .ok (.array (acc.push v), after)
      | other => .error ("expected , or ]", other)
    | .error e => .error e

/-- An object's members (§4) from the next one, `acc` read so far, and the rest after its `}`. -/
def members : Nat → List Char → Array (String × Value) → Reading Value
  | 0, input, _ => .error ("nested deeper than the fuel", input)
  | fuel + 1, input, acc =>
    match input with
    | '"' :: rest =>
      match chars rest [] with
      | .ok (key, afterKey) =>
        match skipWs afterKey with
        | ':' :: afterColon =>
          match value fuel (skipWs afterColon) with
          | .ok (v, afterValue) =>
            match skipWs afterValue with
            | ',' :: after => members fuel (skipWs after) (acc.push (String.ofList key, v))
            | '}' :: after =>
              match table (acc.push (String.ofList key, v)).toList with
              | .ok t => .ok (t, after)
              | .error e => .error (e, input)
            | other => .error ("expected , or }", other)
          | .error e => .error e
        | other => .error ("expected :", other)
      | .error e => .error e
    | other => .error ("expected a string key", other)

end

/-- The value of the JSON text `s` (§2: whitespace, a value, whitespace), or why it is not read and
the rest of the text from where reading stops. -/
def read (s : String) : Except (String × List Char) Value :=
  match value (2 * s.utf8ByteSize + 2) (skipWs s.toList) with
  | .ok (v, rest) =>
    match skipWs rest with
    | [] => .ok v
    | other => .error ("expected the end of the text", other)
  | .error e => .error e

/-- The value of the JSON text `s`, or `none` (see the module docstring). -/
def read? (s : String) : Option Value := (read s).toOption

end Rfc8259

end ExactJSON
