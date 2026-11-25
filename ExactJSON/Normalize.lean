module

public import ExactJSON.Value

public section

namespace ExactJSON

namespace Decimal

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

theorem eq_of_parts {d e : Decimal} (h1 : d.negative = e.negative) (h2 : d.digits = e.digits)
    (h3 : d.exponent = e.exponent) : d = e := by
  cases d
  cases e
  simp_all

theorem digits_mod {d : Decimal} (hd : d.digits ≠ 0) : d.digits % 10 ≠ 0 := by
  have := d.normal
  unfold Normal at this
  rwa [ite_eq_right hd] at this

theorem exponent_zero {d : Decimal} (hd : d.digits = 0) : d.exponent = 0 := by
  have := d.normal
  unfold Normal at this
  rwa [ite_eq_left hd] at this

theorem normal_of_mod {c : Nat} (hc : c % 10 ≠ 0) (q : Int) : Normal c q := by
  unfold Normal
  rw [ite_eq_right (by omega)]
  exact hc

theorem normalize_zero (negative : Bool) (q : Int) : normalize negative 0 q = ⟨negative, 0, 0, by decide⟩ := by
  simp [normalize]

theorem normalize_negative (negative : Bool) (m : Nat) (q : Int) : (normalize negative m q).negative = negative := by
  unfold normalize
  split <;> rfl

theorem normalize_mul_pow (negative : Bool) (c : Nat) (hc : c % 10 ≠ 0) (j : Nat) (q : Int) :
    normalize negative (c * 10 ^ j) (q - j) = ⟨negative, c, q, normal_of_mod hc q⟩ := by
  have hc0 : 0 < c := by omega
  have hpos : c * 10 ^ j ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.mul_pos hc0 (Nat.pow_pos (by decide)))
  unfold normalize
  rw [dite_eq_right hpos]
  exact eq_of_parts (by rfl) (by simp [strip_mul_pow c hc j q]) (by simp [strip_mul_pow c hc j q])

theorem normalize_of_normal (d : Decimal) (hd : d.digits ≠ 0) (j : Nat) :
    normalize d.negative (d.digits * 10 ^ j) (d.exponent - j) = d := by
  rw [normalize_mul_pow _ _ (digits_mod hd)]

theorem eq_zero (d : Decimal) (hd : d.digits = 0) : d = ⟨d.negative, 0, 0, by decide⟩ :=
  eq_of_parts rfl hd (exponent_zero hd)

theorem normalize_of_mod {c : Nat} (hc : c % 10 ≠ 0) (negative : Bool) (q : Int) :
    normalize negative c q = ⟨negative, c, q, normal_of_mod hc q⟩ := by
  have := normalize_mul_pow negative c hc 0 q
  simpa using this

end Decimal

end ExactJSON
