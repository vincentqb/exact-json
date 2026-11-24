module

public import ExactJSON.Codec
public import Lean.Data.Json.FromToJson

/-! # Between `Value` and `Lean.Json`

`Lean.Json` keeps a number as a decimal `JsonNumber` (`mantissa × 10^-exponent`), which can tell
`1` (exponent 0) from `1.0` (exponent 1) but which `Json.compress` prints the same. Here a
`JsonNumber` with exponent 0 is an integer and one with a positive exponent a float, both ways.

`Value.toJson` is exact for valid values except `-0.0` (a `JsonNumber` has no negative zero).
`Value.ofJson?` rounds a decimal with a point to the nearest float, and fails only beyond
binary64's range. These convert between two in-memory forms; neither reads text.

Lean's own `ToJson Float` prints through `Float.toString`, six fixed decimals, so `toJson 1e-7`
is `0` and `toJson 0.1234567` is `0.123457`. `open scoped ExactJSON.ExactFloat` replaces it, in the
scope that opens it (`deriving ToJson` included), by `floatToJson`, which is exact.
-/

public section

namespace ExactJSON

open Lean (Json JsonNumber)

/-- A finite float as the shortest `JsonNumber` that reads back as it, with at least one
fractional digit (so a positive exponent: it reads back as a float); a NaN or an infinity as the
string `"NaN"`, `"Infinity"` or `"-Infinity"`, as `ToValue Float` writes it. -/
def floatToJson (x : Float) : Json :=
  match FloatText.shortest x with
  | none => .str (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity")
  | some d =>
    let m : Int := if d.negative then -(d.digits : Int) else d.digits
    if d.exponent < 0 then .num ⟨m, (-d.exponent).toNat⟩
    else .num ⟨m * 10 ^ (d.exponent.toNat + 1), 1⟩

namespace Value

/-- The `Lean.Json` of a value: integers with exponent 0, floats with a positive one. -/
partial def toJson : Value → Json
  | .null => .null
  | .string s => .str s
  | .integer n => .num ⟨n, 0⟩
  | .float x => floatToJson x
  | .boolean b => .bool b
  | .array items => .arr (items.map toJson)
  | .table members => Json.mkObj (members.toList.map fun (k, v) => (k, toJson v))

/-- The value of a `Lean.Json`: a number with exponent 0 is an integer, any other the nearest
float. (A `Lean.Json` object's keys are in order and distinct, so the value is valid.) -/
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

/-- An exact `ToJson Float` (`floatToJson`), in force where `ExactJSON.ExactFloat` is opened. -/
scoped instance (priority := high) exactToJsonFloat : Lean.ToJson Float := ⟨floatToJson⟩

end ExactFloat

end ExactJSON
