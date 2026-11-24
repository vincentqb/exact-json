module

public import ExactJSON.Codec
public import ExactJSON.Printable
public import ExactJSON.Sound
public import ExactJSON.Cost
public import ExactJSON.Fixed
public import ExactJSON.OfScientific
public import ExactJSON.Write
public import ExactJSON.CodecLaws
public import ExactJSON.LeanJsonLaws
public import ExactJSON.DateTimeLaws
public import ExactJSON.ShortestLaws

public section

namespace ExactJSON

universe u

theorem parse_render_text (s : String) (v : Value) (h : Value.parse s = .ok v) : v.render = s :=
  (parse_sound s v h).1

theorem parse_valid (s : String) (v : Value) (h : Value.parse s = .ok v) : v.Valid :=
  (parse_sound s v h).2

theorem parse_costed (s : String) : (Value.parseCosted s).value = Value.parse s := rfl

theorem parse_linear : ∃ c : Nat, ∀ s : String, (Value.parseCosted s).steps ≤ c * (s.length + 1) :=
  ⟨22, parseCosted_steps⟩

theorem readJson_spec (s : String) : (Value.readJson s).toOption = Rfc8259.read? s := by
  unfold Value.readJson Rfc8259.read?
  split <;> simp_all [Except.toOption]

theorem decode_text {α : Type u} [ToValue α] [FromValue α] (s : String) (a : α)
    (h : decode s = .ok a) : encode a = s := by
  unfold decode at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · split at h
      · rename_i same
        cases h
        unfold encode
        rw [Value.eq_of_beq _ _ same]
        exact parse_render_text s v hv
      · cases h

theorem render_no_control (v : Value) : ∀ c ∈ v.render.toList, 0x20 ≤ c.toNat :=
  printable_render v

theorem read_render (v : Value) (h : v.Valid) : Rfc8259.read? v.render = some v :=
  read_render_of_rounds ofScientificRounds v h

theorem decode_encode {α : Type u} [ToValue α] [FromValue α]
    (lawful : ∀ a : α, fromValue? (toValue a) = .ok a) (valid : ∀ a : α, (toValue a).Valid) (a : α) :
    decode (encode a) = .ok a :=
  decode_encode_of_rounds ofScientificRounds lawful valid a

theorem render_composes (v : Value) : v.render = write (fun x => (Value.float x).render) v :=
  Value.render_eq_write v

theorem render_nonfinite (x : Float) (hx : finiteFloat x = false) :
    (Value.float x).render = if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity" := by
  simp [Value.render, Value.renderTo, floatText, Float.toCanonical?, FloatText.shortest, hx]

theorem render_composes_rejects_null :
    ¬ ∀ (v : Value), (fun (_ : Value) => "null") v = write (fun x => (fun (_ : Value) => "null") (.float x)) v := by
  intro h
  have := h (.boolean true)
  simp [write] at this

theorem render_float_rejects_empty :
    ¬ ∀ (x : Float), finiteFloat x = true →
      ∃ d : Decimal, (fun (_ : Value) => "") (.float x) = d.toFloatText ∧ d.IsShortest x := by
  intro h
  obtain ⟨d, hd, -⟩ := h 0.0 (by decide +kernel)
  have := toFloatText_toList_ne_nil d
  rw [← hd] at this
  exact this rfl

theorem render_nonfinite_rejects_zero :
    ¬ ∀ (x : Float), finiteFloat x = false →
      (fun (_ : Value) => "0.0") (.float x) = if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity" := by
  intro h
  have := h Float.nan (by decide +kernel)
  rw [show Float.nan.isNaN = true by decide +kernel] at this
  simp at this

theorem parse_render_invalid_rejects_null :
    ¬ ∀ (v : Value), ¬ v.Valid →
      ((fun (_ : String) => (Except.ok Value.null : Except String Value)) ((fun (_ : Value) => "") v)).toOption = none := by
  intro h
  have := h (.float Float.nan) (by
    show ¬ (finiteFloat Float.nan = true)
    rw [show finiteFloat Float.nan = false by decide +kernel]
    decide)
  simp [Except.toOption] at this

theorem render_no_control_rejects_newline :
    ¬ ∀ (v : Value), ∀ c ∈ ((fun (_ : Value) => "\n") v).toList, 0x20 ≤ c.toNat := by
  intro h
  exact absurd (h .null '\n' (by decide)) (by decide)

theorem parse_fixed_rejects_constant :
    ¬ ∀ (s : String) (v : Value),
      (fun (_ : String) => (Except.ok Value.null : Except String Value)) s = .ok v ↔
        Rfc8259.read? s = some v ∧ (fun (_ : Value) => "null") v = s := by
  intro h
  have hx : Rfc8259.read? "x" = none := by rfl
  have := ((h "x" .null).mp rfl).1
  rw [hx] at this
  cases this

theorem read_render_rejects_constant :
    ¬ ∀ (v : Value), v.Valid → Rfc8259.read? ((fun (_ : Value) => "x") v) = some v := by
  intro h
  have hx : Rfc8259.read? "x" = none := by rfl
  have := h .null rfl
  rw [hx] at this
  cases this

theorem readJson_spec_rejects_constant :
    ¬ ∀ (s : String),
      ((fun (_ : String) => (Except.ok Value.null : Except String Value)) s).toOption = Rfc8259.read? s := by
  intro h
  have hx : Rfc8259.read? "x" = none := by rfl
  have := h "x"
  rw [hx] at this
  cases this

theorem parse_costed_rejects_mismatch :
    ¬ ∀ (s : String), ((fun (_ : String) => (⟨.error "", 0⟩ : Costed (Except String Value))) s).value =
      (fun (_ : String) => (Except.ok Value.null : Except String Value)) s := by
  intro h
  cases h ""

theorem parse_linear_rejects_quadratic :
    ¬ ∃ c : Nat, ∀ s : String,
      ((fun (s : String) => (⟨.error "", s.length * s.length⟩ : Costed (Except String Value))) s).steps ≤
        c * (s.length + 1) := by
  intro ⟨c, h⟩
  have h' := h (String.ofList (List.replicate (c + 1) 'a'))
  simp only [String.length_ofList, List.length_replicate, Nat.add_mul, Nat.mul_add, Nat.mul_one,
    Nat.one_mul] at h'
  omega

theorem decode_text_rejects_constant :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (s : String) (a : α),
      (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (fromValue? Value.null : Except String β)) s = .ok a →
        (fun {β : Type u} [ToValue β] (_ : β) => "null") a = s := by
  intro h
  exact absurd (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ "x" ⟨⟩ rfl) (by decide)

theorem decode_encode_rejects_failure :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α], (∀ a : α, fromValue? (toValue a) = .ok a) →
      (∀ a : α, (toValue a).Valid) → ∀ (a : α),
        (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (Except.error "wrong" : Except String β))
          ((fun {β : Type u} [ToValue β] (_ : β) => "") a) = .ok a := by
  intro h
  cases @h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ (fun _ => rfl) (fun _ => rfl) ⟨⟩

theorem render_no_control_applies : ∃ (v : Value), ∃ (c : Char), c ∈ v.render.toList :=
  ⟨.null, 'n', by decide +kernel⟩

theorem decode_text_applies :
    ∃ (α : Type u) (_ : ToValue α) (_ : FromValue α) (s : String) (a : α), decode s = .ok a :=
  ⟨PUnit, ⟨fun _ => .null⟩, ⟨fun _ => .ok ⟨⟩⟩, "null", ⟨⟩, by rfl⟩

end ExactJSON
