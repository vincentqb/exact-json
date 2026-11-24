module

public import ExactJSON.Rfc8259

@[expose] public section

namespace ExactJSON

structure Decimal where
  negative : Bool
  digits : Nat
  exponent : Int
  deriving DecidableEq, Repr, Inhabited

namespace Decimal

def zeros (n : Nat) : List Char := List.replicate n '0'

def toFloatText (d : Decimal) : String :=
  let sign : List Char := if d.negative then ['-'] else []
  if d.digits = 0 then String.ofList (sign ++ "0.0".toList)
  else
    let ds := Nat.toDigits 10 d.digits
    let n := ds.length
    let sci : Int := d.exponent + n - 1
    let body : List Char :=
      if -4 ≤ sci ∧ sci < 16 then
        if sci ≥ n - 1 then ds ++ zeros (sci - (n - 1) : Int).toNat ++ ['.', '0']
        else if 0 ≤ sci then ds.take (sci.toNat + 1) ++ ['.'] ++ ds.drop (sci.toNat + 1)
        else ['0', '.'] ++ zeros ((-sci).toNat - 1) ++ ds
      else
        ds.take 1 ++ ['.'] ++ (if n = 1 then ['0'] else ds.drop 1) ++ ['e'] ++ (toString sci).toList
    String.ofList (sign ++ body)

end Decimal

namespace Decimal

def value (d : Decimal) : Rat := (if d.negative then -1 else 1) * (d.digits : Rat) * (10 : Rat) ^ d.exponent

def digitCount (d : Decimal) : Nat := (Nat.toDigits 10 d.digits).length

def ReadsBack (d : Decimal) (x : Float) : Prop := Rfc8259.floatOf? d.negative d.digits d.exponent = some x

end Decimal

def floatValue (x : Float) : Rat :=
  let bits := x.toBits.toNat
  let magnitude : Rat :=
    if bits / 2 ^ 52 % 2 ^ 11 = 0 then ((bits % 2 ^ 52 : Nat) : Rat) * (2 : Rat) ^ (-1074 : Int)
    else ((bits % 2 ^ 52 + 2 ^ 52 : Nat) : Rat) * (2 : Rat) ^ (((bits / 2 ^ 52 % 2 ^ 11 : Nat) : Int) - 1075)
  if bits ≥ 2 ^ 63 then -magnitude else magnitude

def hexChar (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def escapeChar (c : Char) : String :=
  if c = '"' then "\\\""
  else if c = '\\' then "\\\\"
  else if c = '\x08' then "\\b"
  else if c = '\t' then "\\t"
  else if c = '\n' then "\\n"
  else if c = '\x0c' then "\\f"
  else if c = '\r' then "\\r"
  else if c.toNat < 0x20 then
    "\\u00" ++ (hexChar (c.toNat / 16)).toString ++ (hexChar (c.toNat % 16)).toString
  else c.toString

def stringText (s : String) : String := "\"" ++ String.join (s.toList.map escapeChar) ++ "\""

mutual

def write (float : Float → String) : Value → String
  | .null => "null"
  | .boolean b => if b then "true" else "false"
  | .integer n => toString n
  | .float x => float x
  | .string s => stringText s
  | .array ⟨items⟩ => "[" ++ writeItems float items ++ "]"
  | .table ⟨members⟩ => "{" ++ writeMembers float members ++ "}"

def writeItems (float : Float → String) : List Value → String
  | [] => ""
  | [v] => write float v
  | v :: vs => write float v ++ "," ++ writeItems float vs

def writeMembers (float : Float → String) : List (String × Value) → String
  | [] => ""
  | [(k, v)] => stringText k ++ ":" ++ write float v
  | (k, v) :: ms => stringText k ++ ":" ++ write float v ++ "," ++ writeMembers float ms

end

end ExactJSON
