module

public import ExactJSON.Value

public section

namespace ExactJSON

namespace Decimal

theorem strip_normal (m : Nat) (q : Int) (hm : 0 < m) : (strip m q).1 % 10 ≠ 0 ∧ 0 < (strip m q).1 := by
  induction m using Nat.strongRecOn generalizing q with
  | _ m ih =>
    rw [strip_eq]
    split
    · rename_i h
      exact ih (m / 10) (by omega) (q + 1) (by omega)
    · rename_i h
      exact ⟨by omega, hm⟩

theorem strip_mul_pow (c : Nat) (hc : c % 10 ≠ 0) (j : Nat) (q : Int) :
    strip (c * 10 ^ j) (q - j) = (c, q) := by
  induction j generalizing q with
  | zero =>
    rw [strip_eq, ite_eq_right (by simp only [Nat.pow_zero, Nat.mul_one]; omega)]
    simp
  | succ j ih =>
    have hc0 : 0 < c := by omega
    have hpos : 0 < c * 10 ^ (j + 1) := Nat.mul_pos hc0 (Nat.pow_pos (by decide))
    have hmod : c * 10 ^ (j + 1) % 10 = 0 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_mod_left _ _
    rw [strip_eq, ite_eq_left ⟨hpos, hmod⟩]
    have hdiv : c * 10 ^ (j + 1) / 10 = c * 10 ^ j := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      exact Nat.mul_div_cancel _ (by decide)
    rw [hdiv, show q - ((j + 1 : Nat) : Int) + 1 = q - (j : Int) by omega]
    exact ih q

theorem normalize_zero (negative : Bool) (q : Int) : normalize negative 0 q = ⟨negative, 0, 0⟩ := by
  simp [normalize]

theorem normalize_mul_pow (negative : Bool) (c : Nat) (hc : c % 10 ≠ 0) (j : Nat) (q : Int) :
    normalize negative (c * 10 ^ j) (q - j) = ⟨negative, c, q⟩ := by
  have hc0 : 0 < c := by omega
  have hpos : c * 10 ^ j ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos hc0 (Nat.pow_pos (by decide)))
  simp only [normalize, hpos, ite_false, strip_mul_pow c hc j q]

theorem normalize_isNormal (negative : Bool) (m : Nat) (q : Int) : (normalize negative m q).isNormal = true := by
  unfold normalize
  split
  · rfl
  · rename_i hm
    obtain ⟨h1, h2⟩ := strip_normal m q (Nat.pos_of_ne_zero hm)
    simp only [isNormal, Nat.pos_iff_ne_zero.mp h2, ite_false, bne_iff_ne, ne_eq]
    exact h1

theorem normalize_of_isNormal (d : Decimal) (h : d.isNormal = true) (hd : d.digits ≠ 0) (j : Nat) :
    normalize d.negative (d.digits * 10 ^ j) (d.exponent - j) = d := by
  have hc : d.digits % 10 ≠ 0 := by
    simp only [isNormal, hd, ite_false, bne_iff_ne, ne_eq] at h
    exact h
  rw [normalize_mul_pow _ _ hc]

theorem eq_zero_of_isNormal (d : Decimal) (h : d.isNormal = true) (hd : d.digits = 0) :
    d = ⟨d.negative, 0, 0⟩ := by
  simp only [isNormal, hd, ite_true, beq_iff_eq] at h
  cases d
  simp_all

end Decimal

end ExactJSON
