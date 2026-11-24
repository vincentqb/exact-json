module

public import ExactJSON.Value
public import ExactJSON.Rfc8259
public import ExactJSON.Canonical
public import ExactJSON.Calendar
public import ExactJSON.Shapes
meta import SoftwareChallenge

public section

/-!
# Canonical, strictly typed JSON

A canonical text is a JSON text (RFC 8259, as `Rfc8259.read?` reads it) that writing what it holds
gives back: reading takes exactly those texts, and holds what any JSON reader reads in them. A
value's text is `write` of its parts: in strings, escapes for `"`, `\`, control characters and
line separators (`mustEscape`) and no others, an integer in decimal, keys as they come; a finite
float is the shortest decimal that reads back as it, the nearest of those, ties to an even last
digit, laid out by `Decimal.toFloatText`; and an invalid value's text is not read. Every valid
value's text is JSON that holds that value; no text holds a control character (below U+0020, or
U+007F to U+009F) or a line or paragraph separator (U+2028, U+2029); reading JSON in any spelling
holds what RFC 8259 reads in it; JSON Lines is one canonical text a line; typed decoding reads
exactly what typed encoding writes, for any type whose instances are lawful (`LawfulValue`: they
read back what they write, as valid values); each of the library's instances writes the value its
codec law states and reads exactly that, except that a dictionary (`Std.ExtTreeMap String α`)
reads back what it writes; derived instances write the shapes their examples state, and are
lawful; dates and times are written in one RFC 3339 form each and read in that form only; and the
steps the reader counts as it reads (`Value.parseCosted`, whose value is `Value.parse`) are linear
in the text's length.
Not claimed: the readers' error messages; which `deriving` uses fail to compile; the library's
definitions that no law names, and the command line tool beyond the functions it calls; nor that
the steps are the work done: the reader counts them itself, so the law bounds its count, not its
running time.
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

protected def LocalDate.toString : LocalDate → String := sorry

protected def LocalTime.toString : LocalTime → String := sorry

protected def LocalDateTime.toString : LocalDateTime → String := sorry

protected def OffsetDateTime.toString : OffsetDateTime → String := sorry

protected def DateTime.toString : DateTime → String := sorry

def DateTime.parse? : String → Option DateTime := sorry

instance instToValueLocalDate : ToValue LocalDate := sorry

instance instFromValueLocalDate : FromValue LocalDate := sorry

instance instToValueLocalTime : ToValue LocalTime := sorry

instance instFromValueLocalTime : FromValue LocalTime := sorry

instance instToValueLocalDateTime : ToValue LocalDateTime := sorry

instance instFromValueLocalDateTime : FromValue LocalDateTime := sorry

instance instToValueOffsetDateTime : ToValue OffsetDateTime := sorry

instance instFromValueOffsetDateTime : FromValue OffsetDateTime := sorry

instance instToValueDateTime : ToValue DateTime := sorry

instance instFromValueDateTime : FromValue DateTime := sorry

instance Example.instToValuePoint : ToValue Example.Point := sorry

instance Example.instFromValuePoint : FromValue Example.Point := sorry

instance Example.instToValueShape : ToValue Example.Shape := sorry

instance Example.instFromValueShape : FromValue Example.Shape := sorry

instance Example.instToValueEnvelope : ToValue Example.Envelope := sorry

instance Example.instFromValueEnvelope : FromValue Example.Envelope := sorry

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

instance instFromValueOptionOfNotNull {α : Type u} [ToValue α] [FromValue α] [NotNull α] : FromValue (Option α) := sorry

instance instToValueExtTreeMapString {α : Type u} [ToValue α] : ToValue (Std.ExtTreeMap String α) := sorry

instance instFromValueExtTreeMapString {α : Type u} [FromValue α] : FromValue (Std.ExtTreeMap String α) := sorry

theorem parse_fixed (s : String) (v : Value) :
    Value.parse s = .ok v ↔ Rfc8259.read? s = some v ∧ v.render = s := by
  sorry

theorem read_render (v : Value) (h : v.Valid) : Rfc8259.read? v.render = some v := by
  sorry

theorem readJson_spec (s : String) : (Value.readJson s).toOption = Rfc8259.read? s := by
  sorry

theorem render_no_control (v : Value) :
    ∀ c ∈ v.render.toList, 0x20 ≤ c.toNat ∧ ¬(0x7F ≤ c.toNat ∧ c.toNat ≤ 0x9F) ∧ c.toNat ≠ 0x2028 ∧ c.toNat ≠ 0x2029 := by
  sorry

theorem parse_costed (s : String) : (Value.parseCosted s).value = Value.parse s := by
  sorry

theorem parse_linear : ∃ c : Nat, ∀ s : String, (Value.parseCosted s).steps ≤ c * (s.length + 1) := by
  sorry

theorem decode_text {α : Type u} [ToValue α] [FromValue α] (s : String) (a : α)
    (h : decode s = .ok a) : encode a = s := by
  sorry

theorem decode_encode {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] (a : α) :
    decode (encode a) = .ok a := by
  sorry

theorem render_composes (v : Value) : v.render = write (fun x => (Value.float x).render) v := by
  sorry

theorem render_float (x : Float) (hx : finiteFloat x = true) :
    ∃ d : Decimal, (Value.float x).render = d.toFloatText ∧ d.IsShortest x := by
  sorry

theorem parse_render_invalid (v : Value) (h : ¬ v.Valid) : (Value.parse v.render).toOption = none := by
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

theorem codec_extTreeMap {α : Type u} [ToValue α] [FromValue α] (m : Std.ExtTreeMap String α) :
    toValue m = .table (m.toList.map fun (k, a) => (k, toValue a)).toArray ∧
      ((∀ a : α, fromValue? (toValue a) = .ok a) → fromValue? (toValue m) = .ok m) := by
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

theorem decodeLines_encode {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] (as : Array α) :
    decodeLines (encodeLines as) = .ok as := by
  sorry

theorem beq_iff (v w : Value) : (v == w) = true ↔ v = w := by
  sorry

theorem localDate_text (d : LocalDate) : d.toString = d.text := by
  sorry

theorem localTime_text (t : LocalTime) : t.toString = t.text := by
  sorry

theorem localDateTime_text (dt : LocalDateTime) : dt.toString = dt.text := by
  sorry

theorem offsetDateTime_text (dt : OffsetDateTime) : dt.toString = dt.text := by
  sorry

theorem dateTime_text (d : DateTime) : d.toString = d.text := by
  sorry

theorem dateTime_parse (s : String) (d : DateTime) : DateTime.parse? s = some d ↔ d.text = s := by
  sorry

theorem codec_localDate (d : LocalDate) :
    toValue d = .string d.toString ∧ ∀ w : Value, fromValue? w = .ok d ↔ w = .string d.text := by
  sorry

theorem codec_localTime (t : LocalTime) :
    toValue t = .string t.toString ∧ ∀ w : Value, fromValue? w = .ok t ↔ w = .string t.text := by
  sorry

theorem codec_localDateTime (dt : LocalDateTime) :
    toValue dt = .string dt.toString ∧ ∀ w : Value, fromValue? w = .ok dt ↔ w = .string dt.text := by
  sorry

theorem codec_offsetDateTime (dt : OffsetDateTime) :
    toValue dt = .string dt.toString ∧ ∀ w : Value, fromValue? w = .ok dt ↔ w = .string dt.text := by
  sorry

theorem codec_dateTime (d : DateTime) :
    toValue d = .string d.toString ∧ ∀ w : Value, fromValue? w = .ok d ↔ w = .string d.text := by
  sorry

theorem codec_point (p : Example.Point) :
    toValue p = .table ((match p.label? with | none => #[] | some l => #[("label", toValue l)]) ++
      #[("x", toValue p.x), ("y", toValue p.y)]) := by
  sorry

theorem codec_shape (s : Example.Shape) :
    toValue s = (match s with
      | .dot => .string "dot"
      | .circle r => .table #[("circle", .table #[("radius", toValue r)])]
      | .rect w h => .table #[("rect", .table #[("height", toValue h), ("width", toValue w)])]
      | .tagged n => .table #[("tagged", toValue n)]
      | .pair n t => .table #[("pair", .array #[toValue n, toValue t])]
      | .scaled f inner => .table #[("scaled", .table #[("factor", toValue f), ("inner", toValue inner)])]) := by
  sorry

theorem codec_envelope (e : Example.Envelope) :
    toValue e = .table (#[("id", toValue e.id)] ++
      (match e.note? with | none => #[] | some none => #[("note", .null)] | some (some n) => #[("note", toValue n)]) ++
      #[("shape", toValue e.shape)]) := by
  sorry

theorem lawful_examples : LawfulValue Example.Point ∧ LawfulValue Example.Shape ∧ LawfulValue Example.Envelope := by
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
    ¬ ∀ (v : Value), ∀ c ∈ ((fun (_ : Value) => "\n") v).toList,
      0x20 ≤ c.toNat ∧ ¬(0x7F ≤ c.toNat ∧ c.toNat ≤ 0x9F) ∧ c.toNat ≠ 0x2028 ∧ c.toNat ≠ 0x2029 := by
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
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] (a : α),
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

@[kills parse_render_invalid] theorem parse_render_invalid_rejects_null :
    ¬ ∀ (v : Value), ¬ v.Valid →
      ((fun (_ : String) => (Except.ok Value.null : Except String Value)) ((fun (_ : Value) => "") v)).toOption = none := by
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
        ∀ w : Value, @fromValue? (Option α) ((fun {β : Type u} [ToValue β] [FromValue β] [NotNull β] => (⟨fun _ => .ok none⟩ : FromValue (Option β))) (β := α)) w = .ok o ↔
          (match o with | none => w = .null | some a => w ≠ .null ∧ fromValue? w = .ok a) := by
  sorry

@[kills codec_extTreeMap] theorem codec_extTreeMap_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (m : Std.ExtTreeMap String α),
      @toValue (Std.ExtTreeMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.ExtTreeMap String β))) (β := α)) m =
          .table (m.toList.map fun (k, a) => (k, toValue a)).toArray ∧
        ((∀ a : α, fromValue? (toValue a) = .ok a) →
          @fromValue? (Std.ExtTreeMap String α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (Std.ExtTreeMap String β))) (β := α))
            (@toValue (Std.ExtTreeMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.ExtTreeMap String β))) (β := α)) m) = .ok m) := by
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
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] (as : Array α),
        (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (Except.error "" : Except String (Array β)))
          ((fun {β : Type u} [ToValue β] (_ : Array β) => "") as) = .ok as := by
  sorry

@[kills beq_iff] theorem beq_iff_rejects_true :
    ¬ ∀ (v w : Value), @BEq.beq Value ⟨fun _ _ => true⟩ v w = true ↔ v = w := by
  sorry

@[witness decodeLines_text] theorem decodeLines_text_applies :
    ∃ (α : Type u) (_ : ToValue α) (_ : FromValue α) (s : String) (as : Array α), decodeLines s = .ok as := by
  sorry

@[kills localDate_text] theorem localDate_text_rejects_empty :
    ¬ ∀ (d : LocalDate), (fun (_ : LocalDate) => "") d = d.text := by
  sorry

@[kills localTime_text] theorem localTime_text_rejects_empty :
    ¬ ∀ (t : LocalTime), (fun (_ : LocalTime) => "") t = t.text := by
  sorry

@[kills localDateTime_text] theorem localDateTime_text_rejects_empty :
    ¬ ∀ (dt : LocalDateTime), (fun (_ : LocalDateTime) => "") dt = dt.text := by
  sorry

@[kills offsetDateTime_text] theorem offsetDateTime_text_rejects_empty :
    ¬ ∀ (dt : OffsetDateTime), (fun (_ : OffsetDateTime) => "") dt = dt.text := by
  sorry

@[kills dateTime_text] theorem dateTime_text_rejects_empty :
    ¬ ∀ (d : DateTime), (fun (_ : DateTime) => "") d = d.text := by
  sorry

@[kills dateTime_parse] theorem dateTime_parse_rejects_none :
    ¬ ∀ (s : String) (d : DateTime), (fun (_ : String) => (none : Option DateTime)) s = some d ↔ d.text = s := by
  sorry

@[kills codec_localDate] theorem codec_localDate_rejects_null :
    ¬ ∀ (d : LocalDate), @toValue LocalDate ⟨fun _ => .null⟩ d = .string ((fun (_ : LocalDate) => "") d) ∧
      ∀ w : Value, @fromValue? LocalDate ⟨fun _ => .error ""⟩ w = .ok d ↔ w = .string d.text := by
  sorry

@[kills codec_localTime] theorem codec_localTime_rejects_null :
    ¬ ∀ (t : LocalTime), @toValue LocalTime ⟨fun _ => .null⟩ t = .string ((fun (_ : LocalTime) => "") t) ∧
      ∀ w : Value, @fromValue? LocalTime ⟨fun _ => .error ""⟩ w = .ok t ↔ w = .string t.text := by
  sorry

@[kills codec_localDateTime] theorem codec_localDateTime_rejects_null :
    ¬ ∀ (dt : LocalDateTime), @toValue LocalDateTime ⟨fun _ => .null⟩ dt = .string ((fun (_ : LocalDateTime) => "") dt) ∧
      ∀ w : Value, @fromValue? LocalDateTime ⟨fun _ => .error ""⟩ w = .ok dt ↔ w = .string dt.text := by
  sorry

@[kills codec_offsetDateTime] theorem codec_offsetDateTime_rejects_null :
    ¬ ∀ (dt : OffsetDateTime), @toValue OffsetDateTime ⟨fun _ => .null⟩ dt = .string ((fun (_ : OffsetDateTime) => "") dt) ∧
      ∀ w : Value, @fromValue? OffsetDateTime ⟨fun _ => .error ""⟩ w = .ok dt ↔ w = .string dt.text := by
  sorry

@[kills codec_dateTime] theorem codec_dateTime_rejects_null :
    ¬ ∀ (d : DateTime), @toValue DateTime ⟨fun _ => .null⟩ d = .string ((fun (_ : DateTime) => "") d) ∧
      ∀ w : Value, @fromValue? DateTime ⟨fun _ => .error ""⟩ w = .ok d ↔ w = .string d.text := by
  sorry

@[kills codec_point] theorem codec_point_rejects_null :
    ¬ ∀ (p : Example.Point),
      @toValue Example.Point ⟨fun _ => .null⟩ p = .table ((match p.label? with | none => #[] | some l => #[("label", toValue l)]) ++
        #[("x", toValue p.x), ("y", toValue p.y)]) := by
  sorry

@[kills codec_shape] theorem codec_shape_rejects_null :
    ¬ ∀ (s : Example.Shape),
      @toValue Example.Shape ⟨fun _ => .null⟩ s = (match s with
        | .dot => .string "dot"
        | .circle r => .table #[("circle", .table #[("radius", toValue r)])]
        | .rect w h => .table #[("rect", .table #[("height", toValue h), ("width", toValue w)])]
        | .tagged n => .table #[("tagged", toValue n)]
        | .pair n t => .table #[("pair", .array #[toValue n, toValue t])]
        | .scaled f inner =>
          .table #[("scaled", .table #[("factor", toValue f), ("inner", @toValue Example.Shape ⟨fun _ => .null⟩ inner)])]) := by
  sorry

@[kills codec_envelope] theorem codec_envelope_rejects_null :
    ¬ ∀ (e : Example.Envelope),
      @toValue Example.Envelope ⟨fun _ => .null⟩ e = .table (#[("id", toValue e.id)] ++
        (match e.note? with | none => #[] | some none => #[("note", .null)] | some (some n) => #[("note", toValue n)]) ++
        #[("shape", toValue e.shape)]) := by
  sorry

@[kills lawful_examples] theorem lawful_examples_rejects_failure :
    ¬ (@LawfulValue Example.Point Example.instToValuePoint ⟨fun _ => .error ""⟩ ∧ LawfulValue Example.Shape ∧
      LawfulValue Example.Envelope) := by
  sorry

@[witness render_no_control] theorem render_no_control_applies :
    ∃ (v : Value), ∃ (c : Char), c ∈ v.render.toList := by
  sorry

@[witness decode_text] theorem decode_text_applies :
    ∃ (α : Type u) (_ : ToValue α) (_ : FromValue α) (s : String) (a : α), decode s = .ok a := by
  sorry

end ExactJSON
