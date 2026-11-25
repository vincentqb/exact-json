module

public import ExactJSON.Codec
public import ExactJSON.Printable
public import ExactJSON.Write
public import ExactJSON.CodecLaws
public import ExactJSON.Lawful
public import ExactJSON.DateTimeLaws
public import ExactJSON.FloatCodec
public import ExactJSON.ShapesCodec
public import ExactJSON.LinesLaws
public import ExactJSON.TypedLaws

public section

namespace ExactJSON

universe u

theorem render_no_control (v : Value) :
    ∀ c ∈ v.render.toList, 0x20 ≤ c.toNat ∧ ¬(0x7F ≤ c.toNat ∧ c.toNat ≤ 0x9F) ∧ c.toNat ≠ 0x2028 ∧ c.toNat ≠ 0x2029 :=
  printable_render v

theorem read_render (v : Value) (h : v.Valid) : Rfc8259.read? v.render = some v :=
  spec_read_render v h

theorem render_composes (v : Value) : v.render = write v :=
  Value.render_eq_write v

theorem render_composes_rejects_null :
    ¬ ∀ (v : Value), (fun (_ : Value) => "null") v = write v := by
  intro h
  have := h (.boolean true)
  simp [write] at this

theorem render_no_control_rejects_newline :
    ¬ ∀ (v : Value), ∀ c ∈ ((fun (_ : Value) => "\n") v).toList,
      0x20 ≤ c.toNat ∧ ¬(0x7F ≤ c.toNat ∧ c.toNat ≤ 0x9F) ∧ c.toNat ≠ 0x2028 ∧ c.toNat ≠ 0x2029 := by
  intro h
  exact absurd (h .null '\n' (by decide)) (by decide)

theorem read_render_rejects_constant :
    ¬ ∀ (v : Value), v.Valid → Rfc8259.read? ((fun (_ : Value) => "x") v) = some v := by
  intro h
  have hx : Rfc8259.read? "x" = none := by rfl
  have := h .null rfl
  rw [hx] at this
  cases this

theorem render_no_control_applies : ∃ (v : Value), ∃ (c : Char), c ∈ v.render.toList :=
  ⟨.null, 'n', by decide +kernel⟩

end ExactJSON
