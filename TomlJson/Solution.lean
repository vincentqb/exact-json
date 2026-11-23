module

public import TomlJson.Codec
public import TomlJson.Printable

/-! # Proofs of the challenge's headlines, kills and witnesses -/

public section

namespace TomlJson

universe u

theorem parse_render_text (s : String) (v : Value) (h : Value.parse s = .ok v) : v.render = s := by
  unfold Value.parse at h
  split at h
  · cases h
  · split at h
    · rename_i checked
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq] at checked
      exact checked.2
    · cases h

theorem parse_valid (s : String) (v : Value) (h : Value.parse s = .ok v) : v.Valid := by
  unfold Value.parse at h
  split at h
  · cases h
  · split at h
    · rename_i checked
      cases h
      simp only [Bool.and_eq_true] at checked
      exact checked.1
    · cases h

theorem decode_text {α : Type u} [ToValue α] [FromValue α] (s : String) (a : α)
    (h : decode s = .ok a) : encode a = s := by
  unfold decode at h
  split at h
  · cases h
  · rename_i v _
    cases read : (fromValue? v : Except String α) with
    | error e => simp [read, bind, Except.bind] at h
    | ok b =>
      simp only [read, bind, Except.bind] at h
      split at h
      · rename_i same
        cases h
        exact beq_iff_eq.mp same
      · cases h

theorem parse_render_text_rejects_constant :
    ¬ ∀ (s : String) (v : Value), (fun (_ : String) => (Except.ok Value.null : Except String Value)) s = .ok v →
      (fun (_ : Value) => "null") v = s := by
  intro h
  exact absurd (h "x" .null rfl) (by decide)

theorem parse_valid_rejects_infinity :
    ¬ ∀ (s : String) (v : Value),
      (fun (_ : String) => (Except.ok (Value.float (Float.ofBits 0x7FF0000000000000)) : Except String Value)) s =
        .ok v → v.Valid := by
  intro h
  exact absurd (h "" _ rfl) (by decide +kernel)

theorem render_parse_rejects_constant :
    ¬ ∀ (v : Value), v.Valid →
      (fun (_ : String) => (Except.ok Value.null : Except String Value)) ((fun (_ : Value) => "null") v) = .ok v := by
  intro h
  cases h (.boolean true) rfl

theorem render_no_control (v : Value) : ∀ c ∈ v.render.toList, 0x20 ≤ c.toNat :=
  printable_render v

theorem render_no_control_rejects_newline :
    ¬ ∀ (v : Value), ∀ c ∈ ((fun (_ : Value) => "\n") v).toList, 0x20 ≤ c.toNat := by
  intro h
  exact absurd (h .null '\n' (by decide)) (by decide)

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

theorem parse_render_text_applies : ∃ (s : String) (v : Value), Value.parse s = .ok v :=
  ⟨"null", .null, by rfl⟩

theorem parse_valid_applies : ∃ (s : String) (v : Value), Value.parse s = .ok v :=
  parse_render_text_applies

theorem render_no_control_applies : ∃ (v : Value), ∃ (c : Char), c ∈ v.render.toList :=
  ⟨.null, 'n', by decide +kernel⟩

theorem decode_text_applies :
    ∃ (α : Type u) (_ : ToValue α) (_ : FromValue α) (s : String) (a : α), decode s = .ok a :=
  ⟨PUnit, ⟨fun _ => .null⟩, ⟨fun _ => .ok ⟨⟩⟩, "null", ⟨⟩, by rfl⟩

end TomlJson
