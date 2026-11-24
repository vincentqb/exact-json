module

public import ExactJSON.Sound

public section

namespace ExactJSON

theorem beq_iff (v w : Value) : (v == w) = true ↔ v = w :=
  Value.beq_eq_true_iff v w

theorem beq_iff_rejects_true :
    ¬ ∀ (v w : Value), @BEq.beq Value ⟨fun _ _ => true⟩ v w = true ↔ v = w := by
  intro h
  cases (h .null (.boolean true)).mp rfl

end ExactJSON
