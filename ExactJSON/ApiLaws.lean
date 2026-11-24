module

public import ExactJSON.Sound

public section

namespace ExactJSON

theorem beq_iff (v w : Value) : (v == w) = true ↔ v = w :=
  Value.beq_eq_true_iff v w

theorem get?_eq (v : Value) (k : String) :
    v.get? k = (match v with | .table ms => (ms.toList.find? fun m => m.1 == k).map (·.2) | _ => none) := by
  cases v <;> simp [Value.get?]

theorem coe_eq (s : String) (b : Bool) (n : Nat) (v : Value) :
    (Coe.coe s : Value) = .string s ∧ (Coe.coe b : Value) = .boolean b ∧ (OfNat.ofNat n : Value) = .integer n ∧
      toString v = v.render :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem beq_iff_rejects_true :
    ¬ ∀ (v w : Value), @BEq.beq Value ⟨fun _ _ => true⟩ v w = true ↔ v = w := by
  intro h
  cases (h .null (.boolean true)).mp rfl

theorem get?_eq_rejects_none :
    ¬ ∀ (v : Value) (k : String), (fun (_ : Value) (_ : String) => (none : Option Value)) v k =
      (match v with | .table ms => (ms.toList.find? fun m => m.1 == k).map (·.2) | _ => none) := by
  intro h
  have := h (.table #[("a", .null)]) "a"
  simp at this

theorem coe_eq_rejects_null :
    ¬ ∀ (s : String) (b : Bool) (n : Nat) (v : Value),
      @Coe.coe String Value ⟨fun _ => .null⟩ s = .string s ∧ @Coe.coe Bool Value ⟨fun _ => .null⟩ b = .boolean b ∧
        @OfNat.ofNat Value n ((fun {m : Nat} => (⟨.null⟩ : OfNat Value m)) (m := n)) = .integer n ∧
          @ToString.toString Value ⟨fun _ => ""⟩ v = v.render := by
  intro h
  cases (h "" true 0 .null).1

end ExactJSON
