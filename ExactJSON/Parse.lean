module

public import ExactJSON.Render

@[expose] public section

namespace ExactJSON

namespace Parser

inductive Read (α : Type) where
  | ok (a : α) (rest : List Char) (steps : Nat)
  | error (message : String) (rest : List Char) (steps : Nat)

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none

def hex4 (a b c d : Char) : Option Nat := do
  return (← hexValue a) * 4096 + (← hexValue b) * 256 + (← hexValue c) * 16 + (← hexValue d)

def unescape : Char → Option Char
  | '"' => some '"'
  | '\\' => some '\\'
  | 'b' => some '\x08'
  | 't' => some '\t'
  | 'n' => some '\n'
  | 'f' => some '\x0c'
  | 'r' => some '\r'
  | _ => none

def surrogateMessage (written : String) (u : Nat) (after : List Char) : String :=
  let lone := s!"{written} is a lone surrogate, not a character"
  match after with
  | '\\' :: 'u' :: e :: f :: g :: h :: _ =>
    match hex4 e f g h with
    | some low =>
      if u < 0xDC00 && 0xDC00 ≤ low && low < 0xE000 then
        let char := Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (low - 0xDC00))
        s!"write {String.singleton char}, not the surrogate pair {written}{String.ofList ['\\', 'u', e, f, g, h]}"
      else lone
    | none => lone
  | _ => lone

def string : List Char → String → Nat → Read String
  | [], _, steps => .error "unterminated string" [] steps
  | c :: rest, acc, steps =>
    if c == '"' then .ok acc rest (steps + 1)
    else if c == '\\' then
      match rest with
      | 'u' :: a :: b :: d :: e :: r =>
        let written := String.ofList ['\\', 'u', a, b, d, e]
        match hex4 a b d e with
        | none => .error "expected four hexadecimal digits after \\u" (c :: rest) (steps + 6)
        | some u =>
          if 0xD800 ≤ u && u < 0xE000 then .error (surrogateMessage written u r) (c :: rest) (steps + 12)
          else
            let char := Char.ofNat u
            let canonical := pushChar "" char
            if canonical == written then string r (acc.push char) (steps + 12)
            else .error s!"write {canonical}, not {written}" (c :: rest) (steps + 12)
      | e :: r =>
        match unescape e with
        | some u => string r (acc.push u) (steps + 2)
        | none => .error (if e == '/' then "write /, not \\/" else "invalid escape") (c :: rest) (steps + 2)
      | [] => .error "invalid escape" (c :: rest) (steps + 1)
    else if c.val < 0x20 then .error "control character in string (it must be escaped)" (c :: rest) (steps + 1)
    else string rest (acc.push c) (steps + 1)

inductive Grammar where
  | sign
  | whole
  | point
  | fraction
  | exponentMark
  | exponentSign
  | exponent

def Grammar.next (g : Grammar) (c : Char) : Option Grammar :=
  match g with
  | .sign => if c.isDigit then some .whole else none
  | .whole =>
    if c.isDigit then some .whole else if c == '.' then some .point
    else if c == 'e' || c == 'E' then some .exponentMark else none
  | .point => if c.isDigit then some .fraction else none
  | .fraction => if c.isDigit then some .fraction else if c == 'e' || c == 'E' then some .exponentMark else none
  | .exponentMark => if c.isDigit then some .exponent else if c == '-' || c == '+' then some .exponentSign else none
  | .exponentSign => if c.isDigit then some .exponent else none
  | .exponent => if c.isDigit then some .exponent else none

structure Parts where
  negative : Bool := false
  digits : Nat := 0
  fractionDigits : Nat := 0
  isFloat : Bool := false
  exponentNegative : Bool := false
  exponent : Nat := 0
  length : Nat := 0

def Parts.read (p : Parts) (g : Grammar) (c : Char) : Parts :=
  let p := { p with length := p.length + 1 }
  match g with
  | .sign => { p with negative := true }
  | .whole => { p with digits := p.digits * 10 + (c.toNat - 48) }
  | .point | .exponentMark => { p with isFloat := true }
  | .fraction => { p with digits := p.digits * 10 + (c.toNat - 48), fractionDigits := p.fractionDigits + 1 }
  | .exponentSign => { p with exponentNegative := c == '-' }
  | .exponent => { p with exponent := min (p.exponent * 10 + (c.toNat - 48)) (p.length + 400) }

def finish (g : Grammar) (p : Parts) (rest : List Char) (steps : Nat) : Read Parts :=
  match g with
  | .whole | .fraction | .exponent => .ok p rest steps
  | .sign => .error "expected a digit" rest steps
  | .point => .error "expected a digit after the point" rest steps
  | .exponentMark | .exponentSign => .error "expected a digit in the exponent" rest steps

def scan (g : Grammar) (p : Parts) : List Char → Nat → Read Parts
  | [], steps => finish g p [] steps
  | c :: rest, steps =>
    match g.next c with
    | some g' => scan g' (p.read g' c) rest (steps + 1)
    | none => finish g p (c :: rest) (steps + 1)

def Parts.value? (p : Parts) : Option Value :=
  if p.isFloat then
    let exponent : Int := if p.exponentNegative then -(p.exponent : Int) else p.exponent
    (FloatText.ofDecimal? p.negative p.digits (exponent - p.fractionDigits)).map .float
  else some (.integer (if p.negative then -(p.digits : Int) else p.digits))

def lenientScan (input : List Char) (steps : Nat) : Read Parts :=
  match input with
  | '-' :: rest => scan .sign { negative := true, length := 1 } rest steps
  | c :: rest => scan .whole { digits := c.toNat - 48, length := 1 } rest steps
  | [] => .error "expected a value, found the end of the text" [] steps

def lenientError (input : List Char) (steps : Nat) : Read Value :=
  match lenientScan input steps with
  | .error message rest steps => .error message rest steps
  | .ok p rest steps =>
    let suggestion : Read Value := match p.value? with
      | some v => .error s!"not the canonical text of this {if p.isFloat then "float" else "integer"}: write {v.render}" input steps
      | none => .error "a float beyond the range of binary64" input steps
    match rest with
    | c :: _ => if Rfc8259.isNumberChar c then .error s!"a number does not go on with {c}" rest steps else suggestion
    | [] => suggestion

def number (input : List Char) (steps : Nat) : Read Value :=
  let (token, rest) := input.span Rfc8259.isNumberChar
  let steps := steps + 7 * token.length + 7
  match Rfc8259.numberValue token with
  | .ok v =>
    let canonical := v.render
    if canonical.toList == token then .ok v rest steps
    else
      .error s!"not the canonical text of this {if v matches .float _ then "float" else "integer"}: write {canonical}"
        input steps
  | .error _ => lenientError input steps

def keyFollows (acc : Array (String × Value)) (key : String) : Bool :=
  match acc.back? with
  | some (previous, _) => decide (previous < key)
  | none => true

def isWhitespace (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\r'

mutual

def value : Nat → List Char → Nat → Read Value
  | 0, input, steps => .error "nested deeper than the reader's fuel" input steps
  | fuel + 1, input, steps =>
    match input with
    | [] => .error "expected a value, found the end of the text" [] steps
    | '"' :: rest =>
      match string rest "" (steps + 1) with
      | .ok s after steps => .ok (.string s) after steps
      | .error message errorAt steps => .error message errorAt steps
    | '[' :: ']' :: rest => .ok (.array #[]) rest (steps + 2)
    | '[' :: rest => items fuel rest #[] (steps + 1)
    | '{' :: '}' :: rest => .ok (.table #[]) rest (steps + 2)
    | '{' :: rest => members fuel rest #[] (steps + 1)
    | 'n' :: 'u' :: 'l' :: 'l' :: rest => .ok .null rest (steps + 4)
    | 't' :: 'r' :: 'u' :: 'e' :: rest => .ok (.boolean true) rest (steps + 4)
    | 'f' :: 'a' :: 'l' :: 's' :: 'e' :: rest => .ok (.boolean false) rest (steps + 5)
    | c :: rest =>
      if c == '-' || c.isDigit then number (c :: rest) steps
      else if isWhitespace c then .error "canonical text has no whitespace" (c :: rest) (steps + 1)
      else .error "expected a value" (c :: rest) (steps + 1)

def items : Nat → List Char → Array Value → Nat → Read Value
  | 0, input, _, steps => .error "nested deeper than the reader's fuel" input steps
  | fuel + 1, input, acc, steps =>
    match value fuel input steps with
    | .ok item (',' :: rest) steps => items fuel rest (acc.push item) (steps + 1)
    | .ok item (']' :: rest) steps => .ok (.array (acc.push item)) rest (steps + 1)
    | .ok _ rest steps => .error "expected , or ] (canonical text has no whitespace)" rest (steps + 1)
    | .error message rest steps => .error message rest steps

def members : Nat → List Char → Array (String × Value) → Nat → Read Value
  | 0, input, _, steps => .error "nested deeper than the reader's fuel" input steps
  | fuel + 1, input, acc, steps =>
    match input with
    | '"' :: rest =>
      match string rest "" 0 with
      | .error message errorAt keySteps => .error message errorAt (steps + 1 + keySteps)
      | .ok key afterKey keySteps =>
        let steps := steps + 1 + 2 * keySteps
        if keyFollows acc key then
          match afterKey with
          | ':' :: rest =>
            match value fuel rest (steps + 1) with
            | .ok item (',' :: more) steps => members fuel more (acc.push (key, item)) (steps + 1)
            | .ok item ('}' :: more) steps => .ok (.table (acc.push (key, item))) more (steps + 1)
            | .ok _ more steps => .error "expected , or } (canonical text has no whitespace)" more (steps + 1)
            | .error message more steps => .error message more steps
          | more => .error "expected : after a key (canonical text has no whitespace)" more (steps + 1)
        else
          let previous := (acc.back?.map (·.1)).getD ""
          let message :=
            if key == previous then s!"duplicate key {pushString "" key}"
            else s!"keys must increase: {pushString "" key} comes before {pushString "" previous}"
          .error message input steps
    | more => .error "expected a string key" more (steps + 1)

end

def failAt (input : List Char) (message : String) (rest : List Char) (steps : Nat) :
    Costed (Except String Value) :=
  let total := input.length
  let remaining := rest.length
  ⟨.error s!"at character {total - remaining}: {message}", steps + total + remaining⟩

end Parser

namespace Value

def parseCosted (s : String) : Costed (Except String Value) :=
  let input := s.toList
  match Parser.value (2 * s.utf8ByteSize + 2) input s.utf8ByteSize with
  | .ok v [] steps => ⟨.ok v, steps + 1⟩
  | .ok _ rest steps => Parser.failAt input "text after the value (canonical text has no whitespace)" rest (steps + 1)
  | .error message rest steps => Parser.failAt input message rest steps

def parse (s : String) : Except String Value := (parseCosted s).value

def readJson (s : String) : Except String Value :=
  match Rfc8259.read s with
  | .ok v => .ok v
  | .error (message, rest) => .error s!"at character {s.length - rest.length}: {message}"

def parseLines (s : String) : Except String (Array Value) := do
  let parts := s.splitOn "\n"
  let mut out := #[]
  let mut number := 0
  for line in parts, k in [0:parts.length] do
    let last := k + 1 == parts.length
    if last && line.isEmpty then break
    number := number + 1
    match parse line with
    | .ok v => out := out.push v
    | .error e => throw s!"line {number}, {e}"
    if last then throw s!"line {number}: no line feed at its end"
  return out

end Value

end ExactJSON
