module

public import TomlJson.Codec
public import TomlJson.Printable
public import TomlJson.Sound
public import TomlJson.Cost

/-! # Proofs of the challenge's headlines, kills and witnesses -/

public section

namespace TomlJson

universe u

theorem parse_render_text (s : String) (v : Value) (h : Value.parse s = .ok v) : v.render = s :=
  (parse_sound s v h).1

theorem parse_valid (s : String) (v : Value) (h : Value.parse s = .ok v) : v.Valid :=
  (parse_sound s v h).2

theorem parse_costed (s : String) : (Value.parseCosted s).value = Value.parse s := rfl

theorem parse_linear : ∃ c : Nat, ∀ s : String, (Value.parseCosted s).steps ≤ c * (s.length + 1) :=
  ⟨10, parseCosted_steps⟩

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
