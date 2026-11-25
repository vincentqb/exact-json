module

public import ExactJSON.Parse
public import ExactJSON.Float
public import Std.Data.ExtTreeMap

@[expose] public section

namespace ExactJSON

universe u

namespace Value

mutual

def beq : Value → Value → Bool
  | .null, .null => true
  | .string a, .string b => a == b
  | .integer a, .integer b => a == b
  | .decimal a, .decimal b => a == b
  | .boolean a, .boolean b => a == b
  | .array ⟨as⟩, .array ⟨bs⟩ => beqItems as bs
  | .table ⟨as⟩, .table ⟨bs⟩ => beqMembers as bs
  | _, _ => false

def beqItems : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqItems as bs
  | _, _ => false

def beqMembers : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (k, a) :: as, (l, b) :: bs => k == l && beq a b && beqMembers as bs
  | _, _ => false

end

instance : BEq Value := ⟨beq⟩

def get? (v : Value) (key : String) : Option Value :=
  match v with
  | .table members => (members.find? (·.1 == key)).map (·.2)
  | _ => none

def typeName : Value → String
  | .null => "null"
  | .string _ => "string"
  | .integer _ => "integer"
  | .decimal _ => "decimal"
  | .boolean _ => "boolean"
  | .array _ => "array"
  | .table _ => "table"


end Value


def withContext {α : Type u} (context : String) (x : Except String α) : Except String α :=
  x.mapError fun e => s!"{context}: {e}"

def typeMismatch {α : Type u} (what : String) (v : Value) : Except String α :=
  .error s!"expected {what}, found {v.typeName} {v.render}"


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

instance : ToValue Float where
  toValue x :=
    match FloatText.shortest x with
    | some d => .decimal d
    | none => .string (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity")
instance : FromValue Float where
  fromValue?
    | .decimal d =>
      match Rfc8259.floatOf? d.negative d.digits d.exponent with
      | some x =>
        match FloatText.shortest x with
        | some e =>
          if e = d then pure x
          else .error s!"expected the shortest decimal of a float: write {e.text}, not {d.text}"
        | none => .error s!"expected a float, found {d.text}"
      | none => .error s!"a float beyond the range of binary64: {d.text}"
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

instance {α : Type u} [ToValue α] [NotNull α] : ToValue (Option α) :=
  ⟨fun | none => .null | some a => toValue a⟩
instance {α : Type u} [ToValue α] [FromValue α] [NotNull α] : FromValue (Option α) :=
  ⟨fun | .null => pure none | v => some <$> fromValue? v⟩

instance {α : Type u} [ToValue α] : ToValue (Std.ExtTreeMap String α) :=
  ⟨fun m => .table (m.toList.map fun (k, v) => (k, toValue v)).toArray⟩
instance {α : Type u} [FromValue α] : FromValue (Std.ExtTreeMap String α) where
  fromValue?
    | .table members => members.foldlM (init := {}) fun m (k, v) => do
      return m.insert k (← withContext k (fromValue? v))
    | v => typeMismatch "a table" v

instance : NotNull String := ⟨fun _ h => nomatch h⟩
instance : NotNull Bool := ⟨fun _ h => nomatch h⟩
instance : NotNull Int := ⟨fun _ h => nomatch h⟩
instance : NotNull Nat := ⟨fun _ h => nomatch h⟩
instance : NotNull UInt8 := ⟨fun _ h => nomatch h⟩
instance : NotNull UInt16 := ⟨fun _ h => nomatch h⟩
instance : NotNull UInt32 := ⟨fun _ h => nomatch h⟩
instance : NotNull UInt64 := ⟨fun _ h => nomatch h⟩
instance : NotNull Int8 := ⟨fun _ h => nomatch h⟩
instance : NotNull Int16 := ⟨fun _ h => nomatch h⟩
instance : NotNull Int32 := ⟨fun _ h => nomatch h⟩
instance : NotNull Int64 := ⟨fun _ h => nomatch h⟩
instance : NotNull Char := ⟨fun _ h => nomatch h⟩
instance : NotNull Float where
  toValue_ne_null x h := by
    change (match FloatText.shortest x with | some d => _ | none => _) = _ at h
    split at h <;> cases h
instance {α : Type u} [ToValue α] : NotNull (Array α) := ⟨fun _ h => nomatch h⟩
instance {α : Type u} [ToValue α] : NotNull (List α) := ⟨fun _ h => nomatch h⟩
instance {α β : Type u} [ToValue α] [ToValue β] : NotNull (α × β) := ⟨fun _ h => nomatch h⟩
instance {α : Type u} [ToValue α] : NotNull (Std.ExtTreeMap String α) := ⟨fun _ h => nomatch h⟩

def encode {α : Type u} [ToValue α] (a : α) : String := (toValue a).render

def decode {α : Type u} [ToValue α] [FromValue α] (s : String) : Except String α :=
  match Value.parse s with
  | .error e => .error e
  | .ok v =>
    match fromValue? v with
    | .error e => .error e
    | .ok a =>
      if toValue a == v then .ok a
      else .error s!"not the text of a value of this type: it would be written {encode a}"

def encodeLines {α : Type u} [ToValue α] (as : Array α) : String :=
  as.foldl (fun out a => (Value.renderTo out (toValue a)).push '\n') ""

def decodeLines {α : Type u} [ToValue α] [FromValue α] (s : String) : Except String (Array α) :=
  readLines decode 0 #[] (s.splitOn "\n")

end ExactJSON
