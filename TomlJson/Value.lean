module

public import Std.Data.TreeMap

/-! # The data model

A `Value` is a TOML value with its date-times written as strings (see `TomlJson.DateTime`):
exactly the values that have a canonical JSON text. JSON's `null` has no TOML counterpart and is
not a value; an absent table key plays its part.
-/

public section

namespace TomlJson

/-- A TOML value, date-times aside: what one canonical JSON text denotes.

A value is *normal* when every float is finite and every table's keys are strictly increasing in
code point order. `Value.normalize` maps every value to a normal one, `Value.render` writes the
normal form, and `Value.parse` yields only normal values. -/
inductive Value where
  /-- A string; any Lean `String` (Unicode scalar values). -/
  | string (s : String)
  /-- An integer, without bound (TOML requires at least the 64-bit range). -/
  | integer (n : Int)
  /-- An IEEE 754 binary64 float; normal when finite. -/
  | float (x : Float)
  /-- A boolean. -/
  | boolean (b : Bool)
  /-- An array; its items need not share a type (TOML 1.0). -/
  | array (items : Array Value)
  /-- A table, as key-value pairs; normal when the keys strictly increase. -/
  | table (members : Array (String × Value))
  deriving Inhabited, Repr

namespace Value

/-- The empty table. -/
def emptyTable : Value := .table #[]

/-- Whether `x` and `y` are the same float, bit for bit: `-0.0` differs from `0.0`, a NaN equals a
NaN with the same payload. -/
@[inline] def floatSame (x y : Float) : Bool := x.toBits == y.toBits

/-- Structural equality, with floats compared bit for bit and table members in order. -/
protected partial def beq : Value → Value → Bool
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

/-- The string a non-finite float is written as: the spellings Lean's `ToJson Float`,
JavaScript's `Number` and Python's `float` all read. -/
def nonFiniteName (x : Float) : String :=
  if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity"

/-- Table members with strictly increasing keys: sorted by code point, and of several members
with one key, the last. -/
def sortMembers (members : Array (String × Value)) : Array (String × Value) :=
  let increasing := (members.zip (members.extract 1 members.size)).all fun ((k, _), (l, _)) => k < l
  if increasing then members
  else
    let map : Std.TreeMap String Value := members.foldl (fun m (k, v) => m.insert k v) {}
    map.toArray

/-- The normal form: non-finite floats become their names (`"NaN"`, `"Infinity"`,
`"-Infinity"`), tables are sorted by key and keep the last member of each key. -/
partial def normalize : Value → Value
  | .float x => if x.isNaN || x.isInf then .string (nonFiniteName x) else .float x
  | .array items => .array (items.map normalize)
  | .table members => .table (sortMembers (members.map fun (k, v) => (k, normalize v)))
  | v => v

/-- Whether a value is normal (`v.normalize == v`). -/
def isNormal (v : Value) : Bool := v.normalize == v

/-- A table from key-value pairs, normalized: later pairs win over earlier ones with the same
key. -/
def mkTable (members : List (String × Value)) : Value :=
  .table (sortMembers (members.toArray.map fun (k, v) => (k, normalize v)))

/-- The member of a table under `key` (the last, for a table that is not normal), or `none`. -/
def get? (v : Value) (key : String) : Option Value :=
  match v with
  | .table members => (members.findRev? (·.1 == key)).map (·.2)
  | _ => none

/-- The type of a value, in TOML's words. -/
def typeName : Value → String
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
