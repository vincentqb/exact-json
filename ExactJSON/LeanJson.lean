module

public import ExactJSON.Codec
public import Lean.Data.Json.FromToJson

public section

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

partial def toJson : Value → Json
  | .null => .null
  | .string s => .str s
  | .integer n => .num ⟨n, 0⟩
  | .float x => floatToJson x
  | .boolean b => .bool b
  | .array items => .arr (items.map toJson)
  | .table members => Json.mkObj (members.toList.map fun (k, v) => (k, toJson v))

partial def ofJson? : Json → Except String Value
  | .null => pure .null
  | .bool b => pure (.boolean b)
  | .str s => pure (.string s)
  | .num n =>
    if n.exponent == 0 then pure (.integer n.mantissa)
    else match FloatText.ofDecimal? (n.mantissa < 0) n.mantissa.natAbs (-(n.exponent : Int)) with
      | some x => pure (.float x)
      | none => .error s!"{n} is beyond the range of binary64"
  | .arr items => .array <$> items.mapIdxM fun i item => withContext s!"[{i}]" (ofJson? item)
  | .obj members => .table <$> members.foldlM (init := #[]) fun acc k v => do
    return acc.push (k, ← withContext k (ofJson? v))

end Value

namespace ExactFloat

scoped instance (priority := high) exactToJsonFloat : Lean.ToJson Float := ⟨floatToJson⟩

end ExactFloat

end ExactJSON
