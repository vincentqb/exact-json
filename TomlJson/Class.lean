module

public import TomlJson.Parse
public import Std.Data.HashMap
public import Std.Data.TreeMap

/-! # Typed values

`ToValue α` writes a Lean value as a `Value`, `FromValue α` reads one back, and `encode` and
`decode` go through canonical text. Every instance here keeps, and `decode` enforces, the law

    decode s = .ok a  ↔  encode a = s        (for valid `a`, within the reader's limits)

so reading undoes writing, each value has one text, and no other text is read. Reading is strict:
no integer where a float belongs, no unknown key, no `null` where the type has none.

`none` is an absent key as a structure field (or a named constructor argument), and `null`
anywhere else. `Option α` can be written as a value only when `α` never writes `null`
(`NotNull α`): otherwise `none` and `some none` would have one text.
-/

public section

namespace TomlJson

universe u

/-- How a value of type `α` is written as a `Value`. -/
class ToValue (α : Type u) where
  /-- The value `a` is written as. -/
  toValue : α → Value

/-- How a value of type `α` is read from a `Value`. -/
class FromValue (α : Type u) where
  /-- The value of type `α` a `Value` is, or why there is none. -/
  fromValue? : Value → Except String α

/-- `α` is never written as `null`, so `Option α` can write `none` as `null`. Derived instances
come with it. -/
class NotNull (α : Type u) : Prop

export ToValue (toValue)
export FromValue (fromValue?)

/-- Prefix the error of `x`, if any, with where it happened. -/
def withContext {α : Type u} (context : String) (x : Except String α) : Except String α :=
  x.mapError fun e => s!"{context}: {e}"

/-- An error that names what was expected and what was found. -/
def typeMismatch {α : Type u} (what : String) (v : Value) : Except String α :=
  .error s!"expected {what}, found {v.typeName} {v.render}"

instance : ToValue Value := ⟨id⟩
instance : FromValue Value := ⟨pure⟩

instance : ToValue String := ⟨.string⟩
instance : FromValue String := ⟨fun | .string s => pure s | v => typeMismatch "a string" v⟩
instance : NotNull String := ⟨⟩

instance : ToValue Bool := ⟨.boolean⟩
instance : FromValue Bool := ⟨fun | .boolean b => pure b | v => typeMismatch "a boolean" v⟩
instance : NotNull Bool := ⟨⟩

instance : ToValue Int := ⟨.integer⟩
instance : FromValue Int := ⟨fun | .integer n => pure n | v => typeMismatch "an integer" v⟩
instance : NotNull Int := ⟨⟩

instance : ToValue Nat := ⟨fun n => .integer n⟩
instance : FromValue Nat where
  fromValue?
    | .integer n => if 0 ≤ n then pure n.toNat else typeMismatch "a natural number" (.integer n)
    | v => typeMismatch "a natural number" v
instance : NotNull Nat := ⟨⟩

/-- An integer in `[lo, hi]`, for the fixed-width integer types named `name`. -/
def Value.intInRange (lo hi : Int) (name : String) : Value → Except String Int
  | .integer n => if lo ≤ n && n ≤ hi then pure n else typeMismatch s!"an integer in {name}'s range" (.integer n)
  | v => typeMismatch s!"an integer ({name})" v

instance : ToValue UInt8 := ⟨fun n => .integer n.toNat⟩
instance : FromValue UInt8 := ⟨fun v => (Value.intInRange 0 (2 ^ 8 - 1) "UInt8" v).map (·.toNat.toUInt8)⟩
instance : NotNull UInt8 := ⟨⟩
instance : ToValue UInt16 := ⟨fun n => .integer n.toNat⟩
instance : FromValue UInt16 := ⟨fun v => (Value.intInRange 0 (2 ^ 16 - 1) "UInt16" v).map (·.toNat.toUInt16)⟩
instance : NotNull UInt16 := ⟨⟩
instance : ToValue UInt32 := ⟨fun n => .integer n.toNat⟩
instance : FromValue UInt32 := ⟨fun v => (Value.intInRange 0 (2 ^ 32 - 1) "UInt32" v).map (·.toNat.toUInt32)⟩
instance : NotNull UInt32 := ⟨⟩
instance : ToValue UInt64 := ⟨fun n => .integer n.toNat⟩
instance : FromValue UInt64 := ⟨fun v => (Value.intInRange 0 (2 ^ 64 - 1) "UInt64" v).map (·.toNat.toUInt64)⟩
instance : NotNull UInt64 := ⟨⟩
instance : ToValue Int8 := ⟨fun n => .integer n.toInt⟩
instance : FromValue Int8 := ⟨fun v => (Value.intInRange (-2 ^ 7) (2 ^ 7 - 1) "Int8" v).map Int8.ofInt⟩
instance : NotNull Int8 := ⟨⟩
instance : ToValue Int16 := ⟨fun n => .integer n.toInt⟩
instance : FromValue Int16 := ⟨fun v => (Value.intInRange (-2 ^ 15) (2 ^ 15 - 1) "Int16" v).map Int16.ofInt⟩
instance : NotNull Int16 := ⟨⟩
instance : ToValue Int32 := ⟨fun n => .integer n.toInt⟩
instance : FromValue Int32 := ⟨fun v => (Value.intInRange (-2 ^ 31) (2 ^ 31 - 1) "Int32" v).map Int32.ofInt⟩
instance : NotNull Int32 := ⟨⟩
instance : ToValue Int64 := ⟨fun n => .integer n.toInt⟩
instance : FromValue Int64 := ⟨fun v => (Value.intInRange (-2 ^ 63) (2 ^ 63 - 1) "Int64" v).map Int64.ofInt⟩
instance : NotNull Int64 := ⟨⟩

/-- A float: a finite one as itself; a NaN or an infinity, which JSON has no number for, as the
string `"NaN"`, `"Infinity"` or `"-Infinity"`. -/
instance : ToValue Float where
  toValue x :=
    if x.isNaN then .string "NaN"
    else if x.isInf then .string (if x > 0 then "Infinity" else "-Infinity")
    else .float x
instance : FromValue Float where
  fromValue?
    | .float x => pure x
    | .string "NaN" => pure (0.0 / 0.0)
    | .string "Infinity" => pure (1.0 / 0.0)
    | .string "-Infinity" => pure (-1.0 / 0.0)
    | v => typeMismatch "a float" v
instance : NotNull Float := ⟨⟩

instance : ToValue Char := ⟨fun c => .string (String.singleton c)⟩
instance : FromValue Char where
  fromValue?
    | .string s => match s.toList with
      | [c] => pure c
      | _ => typeMismatch "a one-character string" (.string s)
    | v => typeMismatch "a one-character string" v
instance : NotNull Char := ⟨⟩

instance {α : Type u} [ToValue α] : ToValue (Array α) := ⟨fun xs => .array (xs.map toValue)⟩
instance {α : Type u} [FromValue α] : FromValue (Array α) where
  fromValue?
    | .array items => items.mapIdxM fun i v => withContext s!"[{i}]" (fromValue? v)
    | v => typeMismatch "an array" v
instance {α : Type u} : NotNull (Array α) := ⟨⟩

instance {α : Type u} [ToValue α] : ToValue (List α) := ⟨fun xs => toValue xs.toArray⟩
instance {α : Type u} [FromValue α] : FromValue (List α) :=
  ⟨fun v => Array.toList <$> (fromValue? v : Except String (Array α))⟩
instance {α : Type u} : NotNull (List α) := ⟨⟩

instance {α : Type u} {β : Type u} [ToValue α] [ToValue β] : ToValue (α × β) :=
  ⟨fun (a, b) => .array #[toValue a, toValue b]⟩
instance {α : Type u} {β : Type u} [FromValue α] [FromValue β] : FromValue (α × β) where
  fromValue?
    | .array #[a, b] => return (← withContext "[0]" (fromValue? a), ← withContext "[1]" (fromValue? b))
    | v => typeMismatch "an array of two items" v
instance {α : Type u} {β : Type u} : NotNull (α × β) := ⟨⟩

/-- `none` as `null`, `some a` as `a`; only for an `α` that is never `null` itself. -/
instance {α : Type u} [ToValue α] [NotNull α] : ToValue (Option α) :=
  ⟨fun | none => .null | some a => toValue a⟩
instance {α : Type u} [FromValue α] [NotNull α] : FromValue (Option α) :=
  ⟨fun | .null => pure none | v => some <$> fromValue? v⟩

/-- A map with string keys is a table. -/
instance {α : Type u} [ToValue α] : ToValue (Std.TreeMap String α) :=
  ⟨fun m => .table (m.toArray.map fun (k, v) => (k, toValue v))⟩
instance {α : Type u} [FromValue α] : FromValue (Std.TreeMap String α) where
  fromValue?
    | .table members => members.foldlM (init := {}) fun m (k, v) => do
      return m.insert k (← withContext k (fromValue? v))
    | v => typeMismatch "a table" v
instance {α : Type u} : NotNull (Std.TreeMap String α) := ⟨⟩

/-- A hash map with string keys is a table (in key order, as every table is). -/
instance {α : Type u} [ToValue α] : ToValue (Std.HashMap String α) :=
  ⟨fun m => Value.tableOfDistinct (m.toArray.map fun (k, v) => (k, toValue v))⟩
instance {α : Type u} [FromValue α] : FromValue (Std.HashMap String α) where
  fromValue?
    | .table members => members.foldlM (init := {}) fun m (k, v) => do
      return m.insert k (← withContext k (fromValue? v))
    | v => typeMismatch "a table" v
instance {α : Type u} : NotNull (Std.HashMap String α) := ⟨⟩

/-! ## Fields

How a structure's fields (and a constructor's named arguments) are written into a table and read
from one. The derived instances use these, so that a field of type `Option α` is a key that is
there or not (for any `α`: a field `Option (Option α)` is absent, `null` or a value).
-/

/-- How a field of type `α` is written into a table. -/
class ToField (α : Type u) where
  /-- The members `members` and the field `key := a`, if it is written at all. -/
  pushField : Array (String × Value) → String → α → Array (String × Value)

/-- How a field of type `α` is read from a table. -/
class FromField (α : Type u) where
  /-- The field `key` of the table `v`. -/
  getField? : Value → String → Except String α

instance (priority := low) {α : Type u} [ToValue α] : ToField α :=
  ⟨fun members key a => members.push (key, toValue a)⟩

instance {α : Type u} [ToValue α] : ToField (Option α) :=
  ⟨fun members key a => match a with
    | some a => members.push (key, toValue a)
    | none => members⟩

instance (priority := low) {α : Type u} [FromValue α] : FromField α where
  getField? v key := match v.get? key with
    | some item => withContext key (fromValue? item)
    | none => .error s!"missing key {pushString "" key}"

instance {α : Type u} [FromValue α] : FromField (Option α) where
  getField? v key := match v.get? key with
    | some item => some <$> withContext key (fromValue? item)
    | none => pure none

/-! ## Text -/

/-- The canonical text of `a`. -/
def encode {α : Type u} [ToValue α] (a : α) : String := (toValue a).render

/-- The value of type `α` whose canonical text is `s`, or an error. The text must be canonical
(`Value.parse`), must be what `FromValue` reads as an `α`, and must be what that `α` is written
as; this last check makes the law hold for any instance, hand-written ones included. -/
def decode {α : Type u} [ToValue α] [FromValue α] (s : String) : Except String α :=
  match Value.parse s with
  | .error e => .error e
  | .ok v => do
    let a ← fromValue? v
    let again := encode a
    if again == s then return a
    throw s!"not the text of a value of this type: it would be written {again}"

/-- The canonical JSON Lines text of some values. -/
def encodeLines {α : Type u} [ToValue α] (as : Array α) : String :=
  as.foldl (fun out a => (Value.renderTo out (toValue a)).push '\n') ""

/-- The values of canonical JSON Lines text: each line as `decode` reads it, each ended by a line
feed. -/
def decodeLines {α : Type u} [ToValue α] [FromValue α] (s : String) : Except String (Array α) := do
  if s.isEmpty then return #[]
  if !s.endsWith "\n" then throw "JSON Lines text ends with a line feed"
  ((s.splitOn "\n").dropLast.toArray).mapIdxM fun i line =>
    withContext s!"line {i + 1}" (decode line)

end TomlJson
