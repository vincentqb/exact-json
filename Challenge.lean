module

public import ExactJSON.Value
public import ExactJSON.Rfc8259
public import ExactJSON.Canonical
public import Lean.Data.Json.FromToJson
meta import SoftwareChallenge

public section

/-!
# Canonical, strictly typed JSON

A canonical text is a JSON text (RFC 8259, as `Rfc8259.read?` reads it) that writing what it
holds gives back: reading takes exactly those texts, and holds what any JSON reader reads in
them. A value's text is `write` of its parts: minimal escapes in strings, an integer in decimal,
keys as they come; a finite float is the shortest decimal that reads back as it, the nearest of
those, ties to an even last digit, laid out by `Decimal.toFloatText`; a float that is not finite
is `NaN`, `Infinity` or `-Infinity`; and an invalid value's text is not read. Every valid value's
text is JSON that holds that value; no text holds a character below U+0020, so no line feed or
carriage return, and every text is one line of JSON Lines; reading JSON in any spelling holds
what RFC 8259 reads in it; typed decoding reads exactly what typed encoding writes, for any type
whose instances read back what they write; and the steps the reader counts as it reads
(`Value.parseCosted`, whose value is `Value.parse`) are linear in the text's length.
Not claimed: anything about the date-time types, deriving, `exactjson%`, `Lean.Json`, or the
readers' error messages; nor that the steps are the work done: the reader counts them itself, so
the law bounds its count, not its running time.
-/

namespace ExactJSON

universe u

def Value.render : Value → String := sorry

def Value.parse : String → Except String Value := sorry

def Value.parseCosted : String → Costed (Except String Value) := sorry

def Value.readJson : String → Except String Value := sorry

def encode {α : Type u} [ToValue α] : α → String := sorry

def decode {α : Type u} [ToValue α] [FromValue α] : String → Except String α := sorry

def Value.renderLines : Array Value → String := sorry

def Value.parseLines : String → Except String (Array Value) := sorry

def encodeLines {α : Type u} [ToValue α] : Array α → String := sorry

def decodeLines {α : Type u} [ToValue α] [FromValue α] : String → Except String (Array α) := sorry

instance Value.instBEq : BEq Value := sorry

def Value.get? : Value → String → Option Value := sorry

instance Value.instCoeString : Coe String Value := sorry

instance Value.instCoeBool : Coe Bool Value := sorry

instance Value.instOfNat {n : Nat} : OfNat Value n := sorry

instance Value.instToString : ToString Value := sorry

def literalExample : Value := sorry

def literalSplice (n : Nat) (s : String) : Value := sorry

def floatToJson : Float → Lean.Json := sorry

def Value.toJson : Value → Lean.Json := sorry

def Value.ofJson? : Lean.Json → Except String Value := sorry

def ExactFloat.exactToJsonFloat : Lean.ToJson Float := sorry

def canon : Bool → String → Except String String := sorry

instance instToValueValue : ToValue Value := sorry

instance instFromValueValue : FromValue Value := sorry

instance instToValueString : ToValue String := sorry

instance instFromValueString : FromValue String := sorry

instance instToValueBool : ToValue Bool := sorry

instance instFromValueBool : FromValue Bool := sorry

instance instToValueInt : ToValue Int := sorry

instance instFromValueInt : FromValue Int := sorry

instance instToValueNat : ToValue Nat := sorry

instance instFromValueNat : FromValue Nat := sorry

instance instToValueUInt8 : ToValue UInt8 := sorry

instance instFromValueUInt8 : FromValue UInt8 := sorry

instance instToValueUInt16 : ToValue UInt16 := sorry

instance instFromValueUInt16 : FromValue UInt16 := sorry

instance instToValueUInt32 : ToValue UInt32 := sorry

instance instFromValueUInt32 : FromValue UInt32 := sorry

instance instToValueUInt64 : ToValue UInt64 := sorry

instance instFromValueUInt64 : FromValue UInt64 := sorry

instance instToValueInt8 : ToValue Int8 := sorry

instance instFromValueInt8 : FromValue Int8 := sorry

instance instToValueInt16 : ToValue Int16 := sorry

instance instFromValueInt16 : FromValue Int16 := sorry

instance instToValueInt32 : ToValue Int32 := sorry

instance instFromValueInt32 : FromValue Int32 := sorry

instance instToValueInt64 : ToValue Int64 := sorry

instance instFromValueInt64 : FromValue Int64 := sorry

instance instToValueChar : ToValue Char := sorry

instance instFromValueChar : FromValue Char := sorry

instance instToValueFloat : ToValue Float := sorry

instance instFromValueFloat : FromValue Float := sorry

instance instToValueArray {α : Type u} [ToValue α] : ToValue (Array α) := sorry

instance instFromValueArray {α : Type u} [FromValue α] : FromValue (Array α) := sorry

instance instToValueList {α : Type u} [ToValue α] : ToValue (List α) := sorry

instance instFromValueList {α : Type u} [FromValue α] : FromValue (List α) := sorry

instance instToValueProd {α β : Type u} [ToValue α] [ToValue β] : ToValue (α × β) := sorry

instance instFromValueProd {α β : Type u} [FromValue α] [FromValue β] : FromValue (α × β) := sorry

instance instToValueOptionOfNotNull {α : Type u} [ToValue α] [NotNull α] : ToValue (Option α) := sorry

instance instFromValueOptionOfNotNull {α : Type u} [FromValue α] [NotNull α] : FromValue (Option α) := sorry

instance instToValueTreeMapString {α : Type u} [ToValue α] : ToValue (Std.TreeMap String α) := sorry

instance instFromValueTreeMapString {α : Type u} [FromValue α] : FromValue (Std.TreeMap String α) := sorry

instance instToValueHashMapString {α : Type u} [ToValue α] : ToValue (Std.HashMap String α) := sorry

instance instFromValueHashMapString {α : Type u} [FromValue α] : FromValue (Std.HashMap String α) := sorry

theorem parse_fixed (s : String) (v : Value) :
    Value.parse s = .ok v ↔ Rfc8259.read? s = some v ∧ v.render = s := by
  sorry

theorem read_render (v : Value) (h : v.Valid) : Rfc8259.read? v.render = some v := by
  sorry

theorem readJson_spec (s : String) : (Value.readJson s).toOption = Rfc8259.read? s := by
  sorry

theorem render_no_control (v : Value) : ∀ c ∈ v.render.toList, 0x20 ≤ c.toNat := by
  sorry

theorem parse_costed (s : String) : (Value.parseCosted s).value = Value.parse s := by
  sorry

theorem parse_linear : ∃ c : Nat, ∀ s : String, (Value.parseCosted s).steps ≤ c * (s.length + 1) := by
  sorry

theorem decode_text {α : Type u} [ToValue α] [FromValue α] (s : String) (a : α)
    (h : decode s = .ok a) : encode a = s := by
  sorry

theorem decode_encode {α : Type u} [ToValue α] [FromValue α]
    (lawful : ∀ a : α, fromValue? (toValue a) = .ok a) (valid : ∀ a : α, (toValue a).Valid) (a : α) :
    decode (encode a) = .ok a := by
  sorry

theorem render_composes (v : Value) : v.render = write (fun x => (Value.float x).render) v := by
  sorry

theorem render_float (x : Float) (hx : finiteFloat x = true) :
    ∃ d : Decimal, (Value.float x).render = d.toFloatText ∧ d.IsShortest x := by
  sorry

theorem render_nonfinite (x : Float) (hx : finiteFloat x = false) :
    (Value.float x).render = if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity" := by
  sorry

theorem parse_render_invalid (v : Value) (h : ¬ v.Valid) : (Value.parse v.render).toOption = none := by
  sorry

theorem codec_value (v : Value) :
    toValue v = (v : Value) ∧ ∀ w : Value, fromValue? w = .ok v ↔ w = (v : Value) := by
  sorry

theorem codec_string (s : String) :
    toValue s = (.string s : Value) ∧ ∀ w : Value, fromValue? w = .ok s ↔ w = (.string s : Value) := by
  sorry

theorem codec_bool (b : Bool) :
    toValue b = (.boolean b : Value) ∧ ∀ w : Value, fromValue? w = .ok b ↔ w = (.boolean b : Value) := by
  sorry

theorem codec_int (n : Int) :
    toValue n = (.integer n : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n : Value) := by
  sorry

theorem codec_nat (n : Nat) :
    toValue n = (.integer n : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n : Value) := by
  sorry

theorem codec_uInt8 (n : UInt8) :
    toValue n = (.integer n.toNat : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toNat : Value) := by
  sorry

theorem codec_uInt16 (n : UInt16) :
    toValue n = (.integer n.toNat : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toNat : Value) := by
  sorry

theorem codec_uInt32 (n : UInt32) :
    toValue n = (.integer n.toNat : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toNat : Value) := by
  sorry

theorem codec_uInt64 (n : UInt64) :
    toValue n = (.integer n.toNat : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toNat : Value) := by
  sorry

theorem codec_int8 (n : Int8) :
    toValue n = (.integer n.toInt : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toInt : Value) := by
  sorry

theorem codec_int16 (n : Int16) :
    toValue n = (.integer n.toInt : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toInt : Value) := by
  sorry

theorem codec_int32 (n : Int32) :
    toValue n = (.integer n.toInt : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toInt : Value) := by
  sorry

theorem codec_int64 (n : Int64) :
    toValue n = (.integer n.toInt : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toInt : Value) := by
  sorry

theorem codec_char (c : Char) :
    toValue c = (.string (String.singleton c) : Value) ∧ ∀ w : Value, fromValue? w = .ok c ↔ w = (.string (String.singleton c) : Value) := by
  sorry

theorem codec_float (x : Float) :
    toValue x = (if x.isNaN then .string "NaN" else if x.isInf then .string (if x > 0 then "Infinity" else "-Infinity") else .float x : Value) ∧
      ∀ w : Value, fromValue? w = .ok x ↔
        w = .float x ∨ (w = .string "NaN" ∧ x = Float.nan) ∨ (w = .string "Infinity" ∧ x = Float.inf) ∨
        (w = .string "-Infinity" ∧ x = -Float.inf) := by
  sorry

theorem codec_array {α : Type u} [ToValue α] [FromValue α] (xs : Array α) :
    toValue xs = .array (xs.map toValue) ∧
      ∀ w : Value, fromValue? w = .ok xs ↔ ∃ vs : Array Value, w = .array vs ∧ vs.toList.mapM fromValue? = .ok xs.toList := by
  sorry

theorem codec_list {α : Type u} [ToValue α] [FromValue α] (xs : List α) :
    toValue xs = .array (xs.map toValue).toArray ∧
      ∀ w : Value, fromValue? w = .ok xs ↔ ∃ vs : Array Value, w = .array vs ∧ vs.toList.mapM fromValue? = .ok xs := by
  sorry

theorem codec_prod {α β : Type u} [ToValue α] [ToValue β] [FromValue α] [FromValue β] (a : α) (b : β) :
    toValue (a, b) = .array #[toValue a, toValue b] ∧
      ∀ w : Value, fromValue? w = .ok (a, b) ↔
        ∃ va vb : Value, w = .array #[va, vb] ∧ fromValue? va = .ok a ∧ fromValue? vb = .ok b := by
  sorry

theorem codec_option {α : Type u} [ToValue α] [FromValue α] [NotNull α] (o : Option α) :
    toValue o = (match o with | none => .null | some a => toValue a) ∧
      ∀ w : Value, fromValue? w = .ok o ↔
        (match o with | none => w = .null | some a => w ≠ .null ∧ fromValue? w = .ok a) := by
  sorry

theorem codec_treeMap {α : Type u} [ToValue α] [FromValue α] (m : Std.TreeMap String α) :
    toValue m = .table (m.toArray.map fun (k, a) => (k, toValue a)) ∧
      ((∀ a : α, fromValue? (toValue a) = .ok a) →
        ∃ m' : Std.TreeMap String α, fromValue? (toValue m) = .ok m' ∧ m'.toList = m.toList) := by
  sorry

theorem codec_hashMap {α : Type u} [ToValue α] [FromValue α] (m : Std.HashMap String α) :
    (∃ l : List (String × Value), toValue m = .table ⟨l⟩ ∧ keysIncrease (l.map (·.1)) = true ∧
      l.Perm (m.toList.map fun (k, a) => (k, toValue a))) ∧
      ((∀ a : α, fromValue? (toValue a) = .ok a) →
        ∃ m' : Std.HashMap String α, fromValue? (toValue m) = .ok m' ∧ m'.toList.Perm m.toList) := by
  sorry

theorem renderLines_eq (vs : Array Value) :
    Value.renderLines vs = String.join (vs.toList.map fun v => v.render ++ "\n") := by
  sorry

theorem parseLines_fixed (s : String) (vs : Array Value) :
    Value.parseLines s = .ok vs ↔ (∀ v ∈ vs.toList, v.Valid) ∧ Value.renderLines vs = s := by
  sorry

theorem encodeLines_eq {α : Type u} [ToValue α] (as : Array α) :
    encodeLines as = Value.renderLines (as.map toValue) := by
  sorry

theorem decodeLines_text {α : Type u} [ToValue α] [FromValue α] (s : String) (as : Array α)
    (h : decodeLines s = .ok as) : encodeLines as = s := by
  sorry

theorem decodeLines_encode {α : Type u} [ToValue α] [FromValue α]
    (lawful : ∀ a : α, fromValue? (toValue a) = .ok a) (valid : ∀ a : α, (toValue a).Valid) (as : Array α) :
    decodeLines (encodeLines as) = .ok as := by
  sorry

theorem beq_iff (v w : Value) : (v == w) = true ↔ v = w := by
  sorry

theorem get?_eq (v : Value) (k : String) :
    v.get? k = (match v with | .table ms => (ms.toList.find? fun m => m.1 == k).map (·.2) | _ => none) := by
  sorry

theorem coe_eq (s : String) (b : Bool) (n : Nat) (v : Value) :
    (Coe.coe s : Value) = .string s ∧ (Coe.coe b : Value) = .boolean b ∧ (OfNat.ofNat n : Value) = .integer n ∧
      toString v = v.render := by
  sorry

theorem literalExample_eq :
    literalExample = .table #[("a", .integer 1), ("b", .float 2.5),
      ("c", .array #[.null, .boolean true, .string "x"]), ("d", .integer (-3))] := by
  sorry

theorem literalSplice_eq (n : Nat) (s : String) :
    literalSplice n s = .table #[("count", toValue n), ("name", toValue s)] := by
  sorry

theorem floatToJson_finite (x : Float) (d : Decimal) (h : d.IsShortest x) :
    floatToJson x = .num d.toJsonNumber := by
  sorry

theorem floatToJson_nonfinite (x : Float) (hx : finiteFloat x = false) :
    floatToJson x = .str (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity") := by
  sorry

theorem toJson_eq (v : Value) :
    v.toJson = match v with
      | .null => .null
      | .string s => .str s
      | .integer n => .num ⟨n, 0⟩
      | .float x => floatToJson x
      | .boolean b => .bool b
      | .array items => .arr (items.map Value.toJson)
      | .table members => Lean.Json.mkObj (members.toList.map fun (k, w) => (k, w.toJson)) := by
  sorry

theorem ofJson_eq (j : Lean.Json) :
    (Value.ofJson? j).toOption = match j with
      | .null => some .null
      | .bool b => some (.boolean b)
      | .str s => some (.string s)
      | .num n =>
        if n.exponent = 0 then some (.integer n.mantissa)
        else (Rfc8259.floatOf? (decide (n.mantissa < 0)) n.mantissa.natAbs (-(n.exponent : Int))).map .float
      | .arr items => (items.toList.mapM fun i => (Value.ofJson? i).toOption).map fun (l : List Value) => .array l.toArray
      | .obj kvs =>
        ((kvs.toList : List (String × Lean.Json)).mapM fun (p : String × Lean.Json) => (Value.ofJson? p.2).toOption.map (p.1, ·)).map
          fun (l : List (String × Value)) => .table l.toArray := by
  sorry

theorem ofJson_toJson (v : Value) (h : v.Valid) (hz : v.noNegativeZero = true) : Value.ofJson? v.toJson = .ok v := by
  sorry

theorem exactToJsonFloat_eq (x : Float) : ExactFloat.exactToJsonFloat.toJson x = floatToJson x := by
  sorry

theorem canon_text (s : String) : canon false s = (Value.readJson s).map fun v => v.render ++ "\n" := by
  sorry

theorem canon_lines (s : String) :
    (canon true s).toOption =
      ((jsonLines s).mapM fun l => (Value.readJson l).toOption).map fun vs => Value.renderLines vs.toArray := by
  sorry

@[kills parse_fixed] theorem parse_fixed_rejects_constant :
    ¬ ∀ (s : String) (v : Value),
      (fun (_ : String) => (Except.ok Value.null : Except String Value)) s = .ok v ↔
        Rfc8259.read? s = some v ∧ (fun (_ : Value) => "null") v = s := by
  sorry

@[kills read_render] theorem read_render_rejects_constant :
    ¬ ∀ (v : Value), v.Valid → Rfc8259.read? ((fun (_ : Value) => "x") v) = some v := by
  sorry

@[kills readJson_spec] theorem readJson_spec_rejects_constant :
    ¬ ∀ (s : String),
      ((fun (_ : String) => (Except.ok Value.null : Except String Value)) s).toOption = Rfc8259.read? s := by
  sorry

@[kills render_no_control] theorem render_no_control_rejects_newline :
    ¬ ∀ (v : Value), ∀ c ∈ ((fun (_ : Value) => "\n") v).toList, 0x20 ≤ c.toNat := by
  sorry

@[kills parse_costed] theorem parse_costed_rejects_mismatch :
    ¬ ∀ (s : String), ((fun (_ : String) => (⟨.error "", 0⟩ : Costed (Except String Value))) s).value =
      (fun (_ : String) => (Except.ok Value.null : Except String Value)) s := by
  sorry

@[kills parse_linear] theorem parse_linear_rejects_quadratic :
    ¬ ∃ c : Nat, ∀ s : String,
      ((fun (s : String) => (⟨.error "", s.length * s.length⟩ : Costed (Except String Value))) s).steps ≤
        c * (s.length + 1) := by
  sorry

@[kills decode_text] theorem decode_text_rejects_constant :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (s : String) (a : α),
      (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (fromValue? Value.null : Except String β)) s = .ok a →
        (fun {β : Type u} [ToValue β] (_ : β) => "null") a = s := by
  sorry

@[kills decode_encode] theorem decode_encode_rejects_failure :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α], (∀ a : α, fromValue? (toValue a) = .ok a) →
      (∀ a : α, (toValue a).Valid) → ∀ (a : α),
        (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (Except.error "wrong" : Except String β))
          ((fun {β : Type u} [ToValue β] (_ : β) => "") a) = .ok a := by
  sorry

@[kills render_composes] theorem render_composes_rejects_null :
    ¬ ∀ (v : Value), (fun (_ : Value) => "null") v = write (fun x => (fun (_ : Value) => "null") (.float x)) v := by
  sorry

@[kills render_float] theorem render_float_rejects_empty :
    ¬ ∀ (x : Float), finiteFloat x = true →
      ∃ d : Decimal, (fun (_ : Value) => "") (.float x) = d.toFloatText ∧ d.IsShortest x := by
  sorry

@[kills render_nonfinite] theorem render_nonfinite_rejects_zero :
    ¬ ∀ (x : Float), finiteFloat x = false →
      (fun (_ : Value) => "0.0") (.float x) = if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity" := by
  sorry

@[kills parse_render_invalid] theorem parse_render_invalid_rejects_null :
    ¬ ∀ (v : Value), ¬ v.Valid →
      ((fun (_ : String) => (Except.ok Value.null : Except String Value)) ((fun (_ : Value) => "") v)).toOption = none := by
  sorry

@[kills codec_value] theorem codec_value_rejects_null :
    ¬ ∀ (v : Value), @toValue Value ⟨fun _ => .null⟩ v = (v : Value) ∧
      ∀ w : Value, @fromValue? Value ⟨fun _ => .error ""⟩ w = .ok v ↔ w = (v : Value) := by
  sorry

@[kills codec_string] theorem codec_string_rejects_null :
    ¬ ∀ (s : String), @toValue String ⟨fun _ => .null⟩ s = (.string s : Value) ∧
      ∀ w : Value, @fromValue? String ⟨fun _ => .error ""⟩ w = .ok s ↔ w = (.string s : Value) := by
  sorry

@[kills codec_bool] theorem codec_bool_rejects_null :
    ¬ ∀ (b : Bool), @toValue Bool ⟨fun _ => .null⟩ b = (.boolean b : Value) ∧
      ∀ w : Value, @fromValue? Bool ⟨fun _ => .error ""⟩ w = .ok b ↔ w = (.boolean b : Value) := by
  sorry

@[kills codec_int] theorem codec_int_rejects_null :
    ¬ ∀ (n : Int), @toValue Int ⟨fun _ => .null⟩ n = (.integer n : Value) ∧
      ∀ w : Value, @fromValue? Int ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n : Value) := by
  sorry

@[kills codec_nat] theorem codec_nat_rejects_null :
    ¬ ∀ (n : Nat), @toValue Nat ⟨fun _ => .null⟩ n = (.integer n : Value) ∧
      ∀ w : Value, @fromValue? Nat ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n : Value) := by
  sorry

@[kills codec_uInt8] theorem codec_uInt8_rejects_null :
    ¬ ∀ (n : UInt8), @toValue UInt8 ⟨fun _ => .null⟩ n = (.integer n.toNat : Value) ∧
      ∀ w : Value, @fromValue? UInt8 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toNat : Value) := by
  sorry

@[kills codec_uInt16] theorem codec_uInt16_rejects_null :
    ¬ ∀ (n : UInt16), @toValue UInt16 ⟨fun _ => .null⟩ n = (.integer n.toNat : Value) ∧
      ∀ w : Value, @fromValue? UInt16 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toNat : Value) := by
  sorry

@[kills codec_uInt32] theorem codec_uInt32_rejects_null :
    ¬ ∀ (n : UInt32), @toValue UInt32 ⟨fun _ => .null⟩ n = (.integer n.toNat : Value) ∧
      ∀ w : Value, @fromValue? UInt32 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toNat : Value) := by
  sorry

@[kills codec_uInt64] theorem codec_uInt64_rejects_null :
    ¬ ∀ (n : UInt64), @toValue UInt64 ⟨fun _ => .null⟩ n = (.integer n.toNat : Value) ∧
      ∀ w : Value, @fromValue? UInt64 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toNat : Value) := by
  sorry

@[kills codec_int8] theorem codec_int8_rejects_null :
    ¬ ∀ (n : Int8), @toValue Int8 ⟨fun _ => .null⟩ n = (.integer n.toInt : Value) ∧
      ∀ w : Value, @fromValue? Int8 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toInt : Value) := by
  sorry

@[kills codec_int16] theorem codec_int16_rejects_null :
    ¬ ∀ (n : Int16), @toValue Int16 ⟨fun _ => .null⟩ n = (.integer n.toInt : Value) ∧
      ∀ w : Value, @fromValue? Int16 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toInt : Value) := by
  sorry

@[kills codec_int32] theorem codec_int32_rejects_null :
    ¬ ∀ (n : Int32), @toValue Int32 ⟨fun _ => .null⟩ n = (.integer n.toInt : Value) ∧
      ∀ w : Value, @fromValue? Int32 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toInt : Value) := by
  sorry

@[kills codec_int64] theorem codec_int64_rejects_null :
    ¬ ∀ (n : Int64), @toValue Int64 ⟨fun _ => .null⟩ n = (.integer n.toInt : Value) ∧
      ∀ w : Value, @fromValue? Int64 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toInt : Value) := by
  sorry

@[kills codec_char] theorem codec_char_rejects_null :
    ¬ ∀ (c : Char), @toValue Char ⟨fun _ => .null⟩ c = (.string (String.singleton c) : Value) ∧
      ∀ w : Value, @fromValue? Char ⟨fun _ => .error ""⟩ w = .ok c ↔ w = (.string (String.singleton c) : Value) := by
  sorry

@[kills codec_float] theorem codec_float_rejects_null :
    ¬ ∀ (x : Float), @toValue Float ⟨fun _ => .null⟩ x = (if x.isNaN then .string "NaN" else if x.isInf then .string (if x > 0 then "Infinity" else "-Infinity") else .float x : Value) ∧
      ∀ w : Value, @fromValue? Float ⟨fun _ => .error ""⟩ w = .ok x ↔
        w = .float x ∨ (w = .string "NaN" ∧ x = Float.nan) ∨ (w = .string "Infinity" ∧ x = Float.inf) ∨
        (w = .string "-Infinity" ∧ x = -Float.inf) := by
  sorry

@[kills codec_array] theorem codec_array_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (xs : Array α),
      @toValue (Array α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Array β))) (β := α)) xs =
          .array (xs.map toValue) ∧
        ∀ w : Value, @fromValue? (Array α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (Array β))) (β := α)) w = .ok xs ↔
          ∃ vs : Array Value, w = .array vs ∧ vs.toList.mapM fromValue? = .ok xs.toList := by
  sorry

@[kills codec_list] theorem codec_list_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (xs : List α),
      @toValue (List α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (List β))) (β := α)) xs =
          .array (xs.map toValue).toArray ∧
        ∀ w : Value, @fromValue? (List α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (List β))) (β := α)) w = .ok xs ↔
          ∃ vs : Array Value, w = .array vs ∧ vs.toList.mapM fromValue? = .ok xs := by
  sorry

@[kills codec_prod] theorem codec_prod_rejects_null :
    ¬ ∀ {α β : Type u} [ToValue α] [ToValue β] [FromValue α] [FromValue β] (a : α) (b : β),
      @toValue (α × β) ((fun {γ δ : Type u} [ToValue γ] [ToValue δ] => (⟨fun _ => .null⟩ : ToValue (γ × δ))) (γ := α) (δ := β)) (a, b) =
          .array #[toValue a, toValue b] ∧
        ∀ w : Value, @fromValue? (α × β) ((fun {γ δ : Type u} [FromValue γ] [FromValue δ] => (⟨fun _ => .error ""⟩ : FromValue (γ × δ))) (γ := α) (δ := β)) w = .ok (a, b) ↔
          ∃ va vb : Value, w = .array #[va, vb] ∧ fromValue? va = .ok a ∧ fromValue? vb = .ok b := by
  sorry

@[kills codec_option] theorem codec_option_rejects_constant :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] [NotNull α] (o : Option α),
      @toValue (Option α) ((fun {β : Type u} [ToValue β] [NotNull β] => (⟨fun _ => .null⟩ : ToValue (Option β))) (β := α)) o =
          (match o with | none => .null | some a => toValue a) ∧
        ∀ w : Value, @fromValue? (Option α) ((fun {β : Type u} [FromValue β] [NotNull β] => (⟨fun _ => .ok none⟩ : FromValue (Option β))) (β := α)) w = .ok o ↔
          (match o with | none => w = .null | some a => w ≠ .null ∧ fromValue? w = .ok a) := by
  sorry

@[kills codec_treeMap] theorem codec_treeMap_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (m : Std.TreeMap String α),
      @toValue (Std.TreeMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.TreeMap String β))) (β := α)) m =
          .table (m.toArray.map fun (k, a) => (k, toValue a)) ∧
        ((∀ a : α, fromValue? (toValue a) = .ok a) →
          ∃ m' : Std.TreeMap String α,
            @fromValue? (Std.TreeMap String α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (Std.TreeMap String β))) (β := α))
              (@toValue (Std.TreeMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.TreeMap String β))) (β := α)) m) = .ok m' ∧
            m'.toList = m.toList) := by
  sorry

@[kills codec_hashMap] theorem codec_hashMap_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (m : Std.HashMap String α),
      (∃ l : List (String × Value),
        @toValue (Std.HashMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.HashMap String β))) (β := α)) m = .table ⟨l⟩ ∧
          keysIncrease (l.map (·.1)) = true ∧ l.Perm (m.toList.map fun (k, a) => (k, toValue a))) ∧
        ((∀ a : α, fromValue? (toValue a) = .ok a) →
          ∃ m' : Std.HashMap String α,
            @fromValue? (Std.HashMap String α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (Std.HashMap String β))) (β := α))
              (@toValue (Std.HashMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.HashMap String β))) (β := α)) m) = .ok m' ∧
            m'.toList.Perm m.toList) := by
  sorry

@[kills renderLines_eq] theorem renderLines_eq_rejects_empty :
    ¬ ∀ (vs : Array Value), (fun (_ : Array Value) => "") vs = String.join (vs.toList.map fun v => v.render ++ "\n") := by
  sorry

@[kills parseLines_fixed] theorem parseLines_fixed_rejects_empty :
    ¬ ∀ (s : String) (vs : Array Value),
      (fun (_ : String) => (Except.ok #[] : Except String (Array Value))) s = .ok vs ↔
        (∀ v ∈ vs.toList, v.Valid) ∧ (fun (_ : Array Value) => "") vs = s := by
  sorry

@[kills encodeLines_eq] theorem encodeLines_eq_rejects_constant :
    ¬ ∀ {α : Type u} [ToValue α] (as : Array α),
      (fun {β : Type u} [ToValue β] (_ : Array β) => "x") as = (fun (_ : Array Value) => "") (as.map toValue) := by
  sorry

@[kills decodeLines_text] theorem decodeLines_text_rejects_empty :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (s : String) (as : Array α),
      (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (Except.ok #[] : Except String (Array β))) s = .ok as →
        (fun {β : Type u} [ToValue β] (_ : Array β) => "x") as = s := by
  sorry

@[kills decodeLines_encode] theorem decodeLines_encode_rejects_failure :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α], (∀ a : α, fromValue? (toValue a) = .ok a) →
      (∀ a : α, (toValue a).Valid) → ∀ (as : Array α),
        (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (Except.error "" : Except String (Array β)))
          ((fun {β : Type u} [ToValue β] (_ : Array β) => "") as) = .ok as := by
  sorry

@[kills beq_iff] theorem beq_iff_rejects_true :
    ¬ ∀ (v w : Value), @BEq.beq Value ⟨fun _ _ => true⟩ v w = true ↔ v = w := by
  sorry

@[kills get?_eq] theorem get?_eq_rejects_none :
    ¬ ∀ (v : Value) (k : String), (fun (_ : Value) (_ : String) => (none : Option Value)) v k =
      (match v with | .table ms => (ms.toList.find? fun m => m.1 == k).map (·.2) | _ => none) := by
  sorry

@[kills coe_eq] theorem coe_eq_rejects_null :
    ¬ ∀ (s : String) (b : Bool) (n : Nat) (v : Value),
      @Coe.coe String Value ⟨fun _ => .null⟩ s = .string s ∧ @Coe.coe Bool Value ⟨fun _ => .null⟩ b = .boolean b ∧
        @OfNat.ofNat Value n ((fun {m : Nat} => (⟨.null⟩ : OfNat Value m)) (m := n)) = .integer n ∧
          @ToString.toString Value ⟨fun _ => ""⟩ v = v.render := by
  sorry

@[kills literalExample_eq] theorem literalExample_eq_rejects_null :
    ¬ (Value.null : Value) = .table #[("a", .integer 1), ("b", .float 2.5),
      ("c", .array #[.null, .boolean true, .string "x"]), ("d", .integer (-3))] := by
  sorry

@[kills literalSplice_eq] theorem literalSplice_eq_rejects_null :
    ¬ ∀ (n : Nat) (s : String), (fun (_ : Nat) (_ : String) => Value.null) n s =
      .table #[("count", toValue n), ("name", toValue s)] := by
  sorry

@[kills floatToJson_finite] theorem floatToJson_finite_rejects_null :
    ¬ ∀ (x : Float) (d : Decimal), d.IsShortest x → (fun (_ : Float) => Lean.Json.null) x = .num d.toJsonNumber := by
  sorry

@[kills floatToJson_nonfinite] theorem floatToJson_nonfinite_rejects_null :
    ¬ ∀ (x : Float), finiteFloat x = false →
      (fun (_ : Float) => Lean.Json.null) x = .str (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity") := by
  sorry

@[kills toJson_eq] theorem toJson_eq_rejects_null :
    ¬ ∀ (v : Value),
      (fun (_ : Value) => Lean.Json.null) v = match v with
        | .null => .null
        | .string s => .str s
        | .integer n => .num ⟨n, 0⟩
        | .float x => (fun (_ : Float) => Lean.Json.null) x
        | .boolean b => .bool b
        | .array items => .arr (items.map (fun (_ : Value) => Lean.Json.null))
        | .table members => Lean.Json.mkObj (members.toList.map fun (k, w) => (k, (fun (_ : Value) => Lean.Json.null) w)) := by
  sorry

@[kills ofJson_eq] theorem ofJson_eq_rejects_error :
    ¬ ∀ (j : Lean.Json),
      ((fun (_ : Lean.Json) => (Except.error "" : Except String Value)) j).toOption = match j with
        | .null => some .null
        | .bool b => some (.boolean b)
        | .str s => some (.string s)
        | .num n =>
          if n.exponent = 0 then some (.integer n.mantissa)
          else (Rfc8259.floatOf? (decide (n.mantissa < 0)) n.mantissa.natAbs (-(n.exponent : Int))).map .float
        | .arr items =>
          (items.toList.mapM fun i => ((fun (_ : Lean.Json) => (Except.error "" : Except String Value)) i).toOption).map
            fun (l : List Value) => .array l.toArray
        | .obj kvs =>
          ((kvs.toList : List (String × Lean.Json)).mapM fun (p : String × Lean.Json) =>
            ((fun (_ : Lean.Json) => (Except.error "" : Except String Value)) p.2).toOption.map (p.1, ·)).map
              fun (l : List (String × Value)) => .table l.toArray := by
  sorry

@[kills ofJson_toJson] theorem ofJson_toJson_rejects_error :
    ¬ ∀ (v : Value), v.Valid → v.noNegativeZero = true →
      (fun (_ : Lean.Json) => (Except.error "" : Except String Value)) ((fun (_ : Value) => Lean.Json.null) v) = .ok v := by
  sorry

@[kills exactToJsonFloat_eq] theorem exactToJsonFloat_eq_rejects_null :
    ¬ ∀ (x : Float), (⟨fun _ => Lean.Json.null⟩ : Lean.ToJson Float).toJson x = (fun (_ : Float) => Lean.Json.str "") x := by
  sorry

@[kills canon_text] theorem canon_text_rejects_empty :
    ¬ ∀ (s : String), (fun (_ : Bool) (_ : String) => (Except.ok "" : Except String String)) false s =
      ((fun (_ : String) => (Except.ok Value.null : Except String Value)) s).map fun v => (fun (_ : Value) => "null") v ++ "\n" := by
  sorry

@[kills canon_lines] theorem canon_lines_rejects_error :
    ¬ ∀ (s : String),
      ((fun (_ : Bool) (_ : String) => (Except.error "" : Except String String)) true s).toOption =
        ((jsonLines s).mapM fun l => ((fun (_ : String) => (Except.ok Value.null : Except String Value)) l).toOption).map
          fun vs => (fun (_ : Array Value) => "") vs.toArray := by
  sorry

@[witness decodeLines_text] theorem decodeLines_text_applies :
    ∃ (α : Type u) (_ : ToValue α) (_ : FromValue α) (s : String) (as : Array α), decodeLines s = .ok as := by
  sorry

@[witness render_no_control] theorem render_no_control_applies :
    ∃ (v : Value), ∃ (c : Char), c ∈ v.render.toList := by
  sorry

@[witness decode_text] theorem decode_text_applies :
    ∃ (α : Type u) (_ : ToValue α) (_ : FromValue α) (s : String) (a : α), decode s = .ok a := by
  sorry

end ExactJSON
