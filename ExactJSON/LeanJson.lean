module

public import ExactJSON.Codec
public import Lean.Data.Json.FromToJson

@[expose] public section

namespace ExactJSON

open Lean (Json JsonNumber)

def floatToJson (x : Float) : Json :=
  match FloatText.shortest x with
  | none => .str (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity")
  | some d =>
    let m : Int := if d.negative then -(d.digits : Int) else d.digits
    if d.exponent < 0 then .num ⟨m, (-d.exponent).toNat⟩
    else .num ⟨m * 10 ^ (d.exponent.toNat + 1), 1⟩

namespace Value

mutual

def toJson : Value → Json
  | .null => .null
  | .string s => .str s
  | .integer n => .num ⟨n, 0⟩
  | .float x => floatToJson x
  | .boolean b => .bool b
  | .array ⟨items⟩ => .arr (itemsToJson #[] items)
  | .table ⟨members⟩ => Json.mkObj (membersToJson #[] members).toList

def itemsToJson (acc : Array Json) : List Value → Array Json
  | [] => acc
  | v :: rest => itemsToJson (acc.push (toJson v)) rest

def membersToJson (acc : Array (String × Json)) : List (String × Value) → Array (String × Json)
  | [] => acc
  | (k, v) :: rest => membersToJson (acc.push (k, toJson v)) rest

end

mutual

def ofJson? : Json → Except String Value
  | .null => pure .null
  | .bool b => pure (.boolean b)
  | .str s => pure (.string s)
  | .num n =>
    if n.exponent == 0 then pure (.integer n.mantissa)
    else match FloatText.ofDecimal? (n.mantissa < 0) n.mantissa.natAbs (-(n.exponent : Int)) with
      | some x => pure (.float x)
      | none => .error s!"{n} is beyond the range of binary64"
  | .arr ⟨items⟩ => .array <$> itemsOfJson? #[] items
  | .obj ⟨⟨members⟩⟩ => .table <$> membersOfJson? #[] members

def itemsOfJson? (acc : Array Value) : List Json → Except String (Array Value)
  | [] => pure acc
  | item :: rest => do itemsOfJson? (acc.push (← withContext s!"[{acc.size}]" (ofJson? item))) rest

def membersOfJson? (acc : Array (String × Value)) :
    Std.DTreeMap.Internal.Impl String (fun _ => Json) → Except String (Array (String × Value))
  | .leaf => pure acc
  | .inner _ k v l r => do
    let left ← membersOfJson? acc l
    membersOfJson? (left.push (k, ← withContext k (ofJson? v))) r

end

end Value

namespace ExactFloat

scoped instance (priority := high) exactToJsonFloat : Lean.ToJson Float := ⟨floatToJson⟩

end ExactFloat

end ExactJSON
