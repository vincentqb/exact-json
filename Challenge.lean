module

public import TomlJson.Value
meta import SoftwareChallenge

public section

/-!
# Canonical, strictly typed JSON

Reading a text and writing back what was read gives the text; reading yields only valid values,
and every valid value is read back from its text; no text holds a character below U+0020, so no
line feed or carriage return, and every text is one line of JSON Lines; typed decoding reads
exactly what typed encoding writes, for any type whose instances read back what they write; and
the steps the reader counts as it reads (`Value.parseCosted`, whose value is `Value.parse`) are
linear in the text's length.
Not claimed: anything about the date-time types, deriving, `tomljson%`, `Lean.Json`, or the
reader's error messages; nor that the steps are the work done: the reader counts them itself, so
the law bounds its count, not its running time.
-/

namespace TomlJson

universe u

def Value.render : Value → String := sorry

def Value.parse : String → Except String Value := sorry

def Value.parseCosted : String → Costed (Except String Value) := sorry

def encode {α : Type u} [ToValue α] : α → String := sorry

def decode {α : Type u} [ToValue α] [FromValue α] : String → Except String α := sorry

theorem parse_render_text (s : String) (v : Value) (h : Value.parse s = .ok v) : v.render = s := by
  sorry

theorem parse_valid (s : String) (v : Value) (h : Value.parse s = .ok v) : v.Valid := by
  sorry

theorem render_parse (v : Value) (h : v.Valid) : Value.parse v.render = .ok v := by
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

@[kills parse_render_text] theorem parse_render_text_rejects_constant :
    ¬ ∀ (s : String) (v : Value), (fun (_ : String) => (Except.ok Value.null : Except String Value)) s = .ok v →
      (fun (_ : Value) => "null") v = s := by
  sorry

@[kills parse_valid] theorem parse_valid_rejects_infinity :
    ¬ ∀ (s : String) (v : Value),
      (fun (_ : String) => (Except.ok (Value.float (Float.ofBits 0x7FF0000000000000)) : Except String Value)) s =
        .ok v → v.Valid := by
  sorry

@[kills render_parse] theorem render_parse_rejects_constant :
    ¬ ∀ (v : Value), v.Valid →
      (fun (_ : String) => (Except.ok Value.null : Except String Value)) ((fun (_ : Value) => "null") v) = .ok v := by
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

@[witness parse_render_text] theorem parse_render_text_applies :
    ∃ (s : String) (v : Value), Value.parse s = .ok v := by
  sorry

@[witness parse_valid] theorem parse_valid_applies : ∃ (s : String) (v : Value), Value.parse s = .ok v := by
  sorry

@[witness render_no_control] theorem render_no_control_applies :
    ∃ (v : Value), ∃ (c : Char), c ∈ v.render.toList := by
  sorry

@[witness decode_text] theorem decode_text_applies :
    ∃ (α : Type u) (_ : ToValue α) (_ : FromValue α) (s : String) (a : α), decode s = .ok a := by
  sorry

end TomlJson
