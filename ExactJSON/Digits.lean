module

@[expose] public section

namespace ExactJSON

namespace Rfc8259

def digitsValue (ds : List Char) : Nat := Nat.ofDigitChars 10 ds 0

def digitsValueFast (ds : List Char) : Nat :=
  if ds.length ≤ 64 then Nat.ofDigitChars 10 ds 0
  else
    let k := ds.length / 2
    digitsValueFast (ds.take (ds.length - k)) * 10 ^ k + digitsValueFast (ds.drop (ds.length - k))
termination_by ds.length
decreasing_by all_goals (simp only [List.length_take, List.length_drop]; omega)

theorem ofDigitChars_init (m : List Char) (init : Nat) :
    Nat.ofDigitChars 10 m init = init * 10 ^ m.length + Nat.ofDigitChars 10 m 0 := by
  induction m generalizing init with
  | nil => simp [Nat.ofDigitChars_nil]
  | cons c cs ih =>
    simp only [Nat.ofDigitChars_cons, List.length_cons]
    rw [ih, ih (10 * 0 + _)]
    simp only [Nat.mul_zero, Nat.zero_add, Nat.pow_succ]
    rw [Nat.add_mul]
    ac_rfl

theorem digitsValueFast_eq' : ∀ (n : Nat) (ds : List Char), ds.length = n → digitsValueFast ds = digitsValue ds := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro ds hn
    rw [digitsValueFast]
    split
    · rfl
    · rename_i h
      dsimp only
      rw [ih _ (by simp only [List.length_take]; omega) _ rfl, ih _ (by simp only [List.length_drop]; omega) _ rfl]
      unfold digitsValue
      conv => rhs; rw [← List.take_append_drop (ds.length - ds.length / 2) ds]
      rw [Nat.ofDigitChars_append, ofDigitChars_init _ (Nat.ofDigitChars 10 (List.take _ ds) 0), List.length_drop,
        show ds.length - (ds.length - ds.length / 2) = ds.length / 2 by omega]

@[csimp] theorem digitsValue_eq_fast : @digitsValue = @digitsValueFast := by
  funext ds
  exact (digitsValueFast_eq' _ ds rfl).symm

end Rfc8259

namespace Decimal

def strip (m : Nat) (q : Int) : Nat × Int :=
  if h : 0 < m ∧ m % 10 = 0 then strip (m / 10) (q + 1) else (m, q)
termination_by m
decreasing_by omega

def tenSquares : Nat → List (Nat × Nat)
  | 0 => []
  | n + 1 => (10 ^ 2 ^ n, 2 ^ n) :: tenSquares n

def divideOut (m : Nat) (q : Int) : List (Nat × Nat) → Nat × Int
  | [] => (m, q)
  | (p, e) :: ps => if m % p = 0 then divideOut (m / p) (q + e) ps else divideOut m q ps

def stripFast (m : Nat) (q : Int) : Nat × Int :=
  if m = 0 then (m, q) else divideOut m q (tenSquares (m.log2.log2 + 1))

theorem strip_eq (m : Nat) (q : Int) :
    strip m q = if 0 < m ∧ m % 10 = 0 then strip (m / 10) (q + 1) else (m, q) := by
  rw [strip]
  simp only [dite_eq_ite]

theorem strip_div : ∀ (k m : Nat) (q : Int), 0 < m → m % 10 ^ k = 0 → strip m q = strip (m / 10 ^ k) (q + k)
  | 0, m, q, _, _ => by simp
  | k + 1, m, q, hm, hk => by
    have h10 : m % 10 = 0 := by
      rw [Nat.pow_succ] at hk
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans (Nat.dvd_mul_left 10 _) (Nat.dvd_of_mod_eq_zero hk))
    rw [strip_eq, ite_eq_left ⟨hm, h10⟩]
    have hk' : m / 10 % 10 ^ k = 0 := by
      apply Nat.mod_eq_zero_of_dvd
      have := Nat.dvd_of_mod_eq_zero hk
      rw [Nat.pow_succ, Nat.mul_comm] at this
      exact (Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mod_eq_zero h10)).mpr this
    have hpos : 0 < m / 10 := by
      have : 10 ∣ m := Nat.dvd_of_mod_eq_zero h10
      have : 10 ≤ m := Nat.le_of_dvd hm this
      omega
    rw [strip_div k (m / 10) (q + 1) hpos hk', Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (10 ^ k) 10]
    congr 1
    push_cast
    omega

theorem strip_stop (m : Nat) (q : Int) (h : m % 10 ≠ 0) : strip m q = (m, q) := by
  rw [strip_eq, ite_eq_right (by omega)]

theorem divideOut_eq : ∀ (n m : Nat) (q : Int), 0 < m → m % 10 ^ 2 ^ n ≠ 0 →
    divideOut m q (tenSquares n) = strip m q
  | 0, m, q, _, h => by
    simp only [tenSquares, divideOut]
    rw [strip_stop m q (by simpa using h)]
  | n + 1, m, q, hm, h => by
    simp only [tenSquares, divideOut]
    split
    · rename_i hd
      have hpos : 0 < m / 10 ^ 2 ^ n := Nat.div_pos (Nat.le_of_dvd hm (Nat.dvd_of_mod_eq_zero hd))
        (Nat.pow_pos (by decide))
      have h' : m / 10 ^ 2 ^ n % 10 ^ 2 ^ n ≠ 0 := by
        intro h0
        apply h
        apply Nat.mod_eq_zero_of_dvd
        rw [Nat.pow_succ, Nat.pow_mul, Nat.pow_two]
        exact (Nat.dvd_div_iff_mul_dvd (Nat.dvd_of_mod_eq_zero hd)).mp (Nat.dvd_of_mod_eq_zero h0)
      rw [divideOut_eq n _ _ hpos h', strip_div (2 ^ n) m q hm hd]
    · rename_i hd
      exact divideOut_eq n m q hm hd

theorem stripFast_eq (m : Nat) (q : Int) : stripFast m q = strip m q := by
  unfold stripFast
  split
  · rename_i h
    subst h
    rw [strip_eq, ite_eq_right (by omega)]
  · rename_i h
    apply divideOut_eq _ _ _ (Nat.pos_of_ne_zero h)
    intro h0
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero h) (Nat.dvd_of_mod_eq_zero h0)
    have h1 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
    have h3 : m.log2 < 2 ^ (m.log2.log2 + 1) := Nat.lt_log2_self
    have h2 : 2 ^ (m.log2 + 1) ≤ 10 ^ 2 ^ (m.log2.log2 + 1) := by
      calc 2 ^ (m.log2 + 1) ≤ 2 ^ 2 ^ (m.log2.log2 + 1) := Nat.pow_le_pow_right (by decide) h3
        _ ≤ 10 ^ 2 ^ (m.log2.log2 + 1) := Nat.pow_le_pow_left (by decide) _
    omega

@[csimp] theorem strip_eq_fast : @strip = @stripFast := by
  funext m q
  exact (stripFast_eq m q).symm

end Decimal

end ExactJSON
