module

public import TomlJson.Parse
public import Std.Data.HashMap

/-! # Typed values

`ToValue α` and `FromValue α` say how a Lean type is written as a `Value` and read back. Each
instance here keeps the law

* `fromValue? (toValue a) = .ok a` (for floats, up to a NaN's payload),

and `decodeCanonical` adds the converse: it accepts a text only if it is canonical *and*
re-encoding what it decoded gives the text back. So, for any `s`,
`decodeCanonical s = .ok a → encode a = s`: the property `text = encode (decode text)`.

`FromValue` itself is lenient where foreign producers differ harmlessly: an integer is accepted
where a float is expected (JavaScript writes `1.0` as `1`), unknown table keys are ignored, and a
missing key reads as `none` for an `Option` field.

`Option` has no `ToValue` instance: TOML has no null, so an absent value is an absent table key.
Structure fields of type `Option α` (see `ToField`) are omitted when `none`.
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
  /-- The value of type `α` a `Value` denotes, or why there is none. -/
  fromValue? : Value → Except String α

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

instance : ToValue Bool := ⟨.boolean⟩
instance : FromValue Bool := ⟨fun | .boolean b => pure b | v => typeMismatch "a boolean" v⟩

instance : ToValue Int := ⟨.integer⟩
instance : FromValue Int := ⟨fun | .integer n => pure n | v => typeMismatch "an integer" v⟩

instance : ToValue Nat := ⟨fun n => .integer n⟩
instance : FromValue Nat where
  fromValue?
    | .integer n => if 0 ≤ n then pure n.toNat else typeMismatch "a natural number" (.integer n)
    | v => typeMismatch "a natural number" v

/-- An integer in `[lo, hi]`, for the fixed-width integer types named `name`. -/
def Value.intInRange (lo hi : Int) (name : String) : Value → Except String Int
  | .integer n => if lo ≤ n && n ≤ hi then pure n else typeMismatch s!"an integer in {name}'s range" (.integer n)
  | v => typeMismatch s!"an integer ({name})" v

instance : ToValue UInt8 := ⟨fun n => .integer n.toNat⟩
instance : FromValue UInt8 := ⟨fun v => (Value.intInRange 0 (2 ^ 8 - 1) "UInt8" v).map (·.toNat.toUInt8)⟩
instance : ToValue UInt16 := ⟨fun n => .integer n.toNat⟩
instance : FromValue UInt16 := ⟨fun v => (Value.intInRange 0 (2 ^ 16 - 1) "UInt16" v).map (·.toNat.toUInt16)⟩
instance : ToValue UInt32 := ⟨fun n => .integer n.toNat⟩
instance : FromValue UInt32 := ⟨fun v => (Value.intInRange 0 (2 ^ 32 - 1) "UInt32" v).map (·.toNat.toUInt32)⟩
instance : ToValue UInt64 := ⟨fun n => .integer n.toNat⟩
instance : FromValue UInt64 := ⟨fun v => (Value.intInRange 0 (2 ^ 64 - 1) "UInt64" v).map (·.toNat.toUInt64)⟩
instance : ToValue Int8 := ⟨fun n => .integer n.toInt⟩
instance : FromValue Int8 := ⟨fun v => (Value.intInRange (-2 ^ 7) (2 ^ 7 - 1) "Int8" v).map Int8.ofInt⟩
instance : ToValue Int16 := ⟨fun n => .integer n.toInt⟩
instance : FromValue Int16 := ⟨fun v => (Value.intInRange (-2 ^ 15) (2 ^ 15 - 1) "Int16" v).map Int16.ofInt⟩
instance : ToValue Int32 := ⟨fun n => .integer n.toInt⟩
instance : FromValue Int32 := ⟨fun v => (Value.intInRange (-2 ^ 31) (2 ^ 31 - 1) "Int32" v).map Int32.ofInt⟩
instance : ToValue Int64 := ⟨fun n => .integer n.toInt⟩
instance : FromValue Int64 := ⟨fun v => (Value.intInRange (-2 ^ 63) (2 ^ 63 - 1) "Int64" v).map Int64.ofInt⟩

/-- A float: a finite one as itself, a NaN or an infinity as its name (`"NaN"`, `"Infinity"`,
`"-Infinity"`), the strings Lean's `FromJson Float`, JavaScript and Python read as such. -/
instance : ToValue Float := ⟨fun x => (Value.float x).normalize⟩
instance : FromValue Float where
  fromValue?
    | .float x => pure x
    | .integer n =>
      let x := Float.ofInt n
      if x.isInf then typeMismatch "a float (this integer is beyond binary64's range)" (.integer n)
      else pure x
    | .string "NaN" => pure (0.0 / 0.0)
    | .string "Infinity" => pure (1.0 / 0.0)
    | .string "-Infinity" => pure (-1.0 / 0.0)
    | v => typeMismatch "a float" v

instance : ToValue Char := ⟨fun c => .string (String.singleton c)⟩
instance : FromValue Char where
  fromValue?
    | .string s => match s.toList with
      | [c] => pure c
      | _ => typeMismatch "a one-character string" (.string s)
    | v => typeMismatch "a one-character string" v

instance {α : Type u} [ToValue α] : ToValue (Array α) := ⟨fun xs => .array (xs.map toValue)⟩
instance {α : Type u} [FromValue α] : FromValue (Array α) where
  fromValue?
    | .array items => items.mapIdxM fun i v => withContext s!"[{i}]" (fromValue? v)
    | v => typeMismatch "an array" v

instance {α : Type u} [ToValue α] : ToValue (List α) := ⟨fun xs => toValue xs.toArray⟩
instance {α : Type u} [FromValue α] : FromValue (List α) :=
  ⟨fun v => Array.toList <$> (fromValue? v : Except String (Array α))⟩

instance {α : Type u} {β : Type u} [ToValue α] [ToValue β] : ToValue (α × β) :=
  ⟨fun (a, b) => .array #[toValue a, toValue b]⟩
instance {α : Type u} {β : Type u} [FromValue α] [FromValue β] : FromValue (α × β) where
  fromValue?
    | .array #[a, b] => return (← withContext "[0]" (fromValue? a), ← withContext "[1]" (fromValue? b))
    | v => typeMismatch "an array of two items" v

/-- A map with string keys is a table. -/
instance {α : Type u} [ToValue α] : ToValue (Std.TreeMap String α) :=
  ⟨fun m => .table (m.toArray.map fun (k, v) => (k, toValue v))⟩
instance {α : Type u} [FromValue α] : FromValue (Std.TreeMap String α) where
  fromValue?
    | .table members => members.foldlM (init := {}) fun m (k, v) => do
      return m.insert k (← withContext k (fromValue? v))
    | v => typeMismatch "a table" v

/-- A hash map with string keys is a table (written in key order, as every table is). -/
instance {α : Type u} [ToValue α] : ToValue (Std.HashMap String α) :=
  ⟨fun m => .table (Value.sortMembers (m.toArray.map fun (k, v) => (k, toValue v)))⟩
instance {α : Type u} [FromValue α] : FromValue (Std.HashMap String α) where
  fromValue?
    | .table members => members.foldlM (init := {}) fun m (k, v) => do
      return m.insert k (← withContext k (fromValue? v))
    | v => typeMismatch "a table" v

/-! ## Fields

How a structure's fields (and a constructor's named arguments) are written into a table and read
from one. The derived instances use these, so that a field of type `Option α` is an optional key.
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

/-- The value of type `α` a JSON text denotes, read leniently: any JSON text `Value.parse` takes,
and `FromValue`'s coercions. -/
def decode {α : Type u} [FromValue α] (s : String) : Except String α :=
  match Value.parse s with
  | .ok v => fromValue? v
  | .error e => .error e

/-- The value of type `α` whose canonical text is `s`, or an error: `s` must be canonical
(`Value.parseCanonical`), and encoding what it decodes to must give `s` back (no ignored key, no
integer where a float belongs). So `decodeCanonical s = .ok a` implies `encode a = s`. -/
def decodeCanonical {α : Type u} [ToValue α] [FromValue α] (s : String) : Except String α :=
  match Value.parseCanonical s with
  | .error e => .error e
  | .ok v => do
    let a ← fromValue? v
    let again := encode a
    if again == s then return a
    throw s!"canonical JSON, but not the canonical encoding of a value of this type: it encodes back as {again}"

/-- The canonical JSON Lines text of some values. -/
def encodeLines {α : Type u} [ToValue α] (as : Array α) : String :=
  as.foldl (fun out a => (Value.renderTo out (toValue a)).push '\n') ""

/-- The values of JSON Lines text, read leniently (see `Value.parseLines` and `decode`). -/
def decodeLines {α : Type u} [FromValue α] (s : String) : Except String (Array α) :=
  match Value.parseLines s with
  | .ok vs => vs.mapIdxM fun i v => withContext s!"record {i + 1}" (fromValue? v)
  | .error e => .error e

/-- The values of canonical JSON Lines text: each line as `decodeCanonical` reads it. -/
def decodeLinesCanonical {α : Type u} [ToValue α] [FromValue α] (s : String) :
    Except String (Array α) := do
  if s.isEmpty then return #[]
  if !s.endsWith "\n" then throw "canonical JSON Lines text ends with a line feed"
  ((s.splitOn "\n").dropLast.toArray).mapIdxM fun i line =>
    withContext s!"line {i + 1}" (decodeCanonical line)

end TomlJson
