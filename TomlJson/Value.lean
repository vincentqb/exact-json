module

/-! # The data model

A `Value` is the untyped form of a canonical text: JSON whose numbers are either integers or
binary64 floats. Typed values (structures, `Float`, dates, …) are written through it
(`TomlJson.ToValue`), and read from it (`TomlJson.FromValue`).
-/

public section

namespace TomlJson

/-- A JSON value whose numbers are integers or floats.

A value is *valid* when its floats are finite and each table's keys strictly increase in code
point order: exactly the values that have a canonical text. `Value.render` writes any value as it
is, so an invalid one gets a text that `Value.parse` rejects, never another value's text. -/
inductive Value where
  /-- `null`. -/
  | null
  /-- A string; any Lean `String` (Unicode scalar values). -/
  | string (s : String)
  /-- An integer, without bound. -/
  | integer (n : Int)
  /-- An IEEE 754 binary64 float; valid when finite. -/
  | float (x : Float)
  /-- A boolean. -/
  | boolean (b : Bool)
  /-- An array; its items need not share a type. -/
  | array (items : Array Value)
  /-- A table, as key-value pairs; valid when the keys strictly increase. -/
  | table (members : Array (String × Value))
  deriving Inhabited, Repr

namespace Value

/-- Whether `x` and `y` are the same float, bit for bit: `-0.0` differs from `0.0`, a NaN equals a
NaN with the same payload. -/
@[inline] def floatSame (x y : Float) : Bool := x.toBits == y.toBits

/-- Structural equality, with floats compared bit for bit and table members in order. -/
protected partial def beq : Value → Value → Bool
  | .null, .null => true
  | .string a, .string b => a == b
  | .integer a, .integer b => a == b
  | .float a, .float b => floatSame a b
  | .boolean a, .boolean b => a == b
  | .array as, .array bs =>
    as.size == bs.size && (as.zip bs).all fun (a, b) => Value.beq a b
  | .table as, .table bs =>
    as.size == bs.size && (as.zip bs).all fun ((k, a), (l, b)) => k == l && Value.beq a b
  | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

/-- Whether the keys strictly increase (in code point order, Lean's `String` order). -/
def keysIncrease (members : Array (String × Value)) : Bool :=
  (members.zip (members.extract 1 members.size)).all fun ((k, _), (l, _)) => k < l

/-- Whether a value has a canonical text: every float finite, every table's keys strictly
increasing. -/
partial def isValid : Value → Bool
  | .float x => !(x.isNaN || x.isInf)
  | .array items => items.all isValid
  | .table members => keysIncrease members && members.all (isValid ·.2)
  | _ => true

/-- A table of members whose keys are distinct (as a map's are), put in key order. -/
def tableOfDistinct (members : Array (String × Value)) : Value :=
  .table (members.qsort (·.1 < ·.1))

/-- The member of a table under `key`, or `none`. -/
def get? (v : Value) (key : String) : Option Value :=
  match v with
  | .table members => (members.find? (·.1 == key)).map (·.2)
  | _ => none

/-- The type of a value, for messages. -/
def typeName : Value → String
  | .null => "null"
  | .string _ => "string"
  | .integer _ => "integer"
  | .float _ => "float"
  | .boolean _ => "boolean"
  | .array _ => "array"
  | .table _ => "table"

instance : Coe String Value := ⟨.string⟩
instance : Coe Bool Value := ⟨.boolean⟩
instance {n : Nat} : OfNat Value n := ⟨.integer n⟩

end Value

end TomlJson
