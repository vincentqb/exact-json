module

public import ExactJSON.Value

@[expose] public section

namespace ExactJSON

namespace Rfc8259

abbrev Reading (α : Type) := Except (String × List Char) (α × List Char)

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

def skipWs : List Char → List Char
  | c :: rest => if isWs c then skipWs rest else c :: rest
  | [] => []

def isNumberChar (c : Char) : Bool :=
  c.isDigit || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E'

def digitsValue (ds : List Char) : Nat := Nat.ofDigitChars 10 ds 0

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

def numberSign : List Char → Bool × List Char
  | '-' :: t => (true, t)
  | t => (false, t)

def exponentSign : List Char → Bool × List Char
  | '-' :: t => (true, t)
  | '+' :: t => (false, t)
  | t => (false, t)

def numberValue (token : List Char) : Except String Value :=
  let (negative, t) := numberSign token
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
            let (minus, t) := exponentSign t
            let (ds, t) := t.span Char.isDigit
            let size := digitsValue ds
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
        | _, _ => .ok (.decimal (Decimal.normalize negative m (exponent.getD 0 - ((fraction.getD []).length : Int))))

def hexValue? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

def hex4? (a b c d : Char) : Option Nat := do
  return (← hexValue? a) * 4096 + (← hexValue? b) * 256 + (← hexValue? c) * 16 + (← hexValue? d)

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

def neighboursDistinct : List (String × Value) → Bool
  | a :: b :: rest => a.1 != b.1 && neighboursDistinct (b :: rest)
  | _ => true

def table (members : List (String × Value)) : Except String Value :=
  let sorted := members.mergeSort fun a b => decide (a.1 ≤ b.1)
  if neighboursDistinct sorted then .ok (.table sorted.toArray)
  else .error "a key repeats"

mutual

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

def read (s : String) : Except (String × List Char) Value :=
  match value (2 * s.utf8ByteSize + 2) (skipWs s.toList) with
  | .ok (v, rest) =>
    match skipWs rest with
    | [] => .ok v
    | other => .error ("expected the end of the text", other)
  | .error e => .error e

def read? (s : String) : Option Value := (read s).toOption

end Rfc8259

end ExactJSON
