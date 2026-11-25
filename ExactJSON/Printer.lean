module

public import ExactJSON.Canonical

@[expose] public section

namespace ExactJSON

def digitsExactly : Nat → Nat → List Char
  | 0, _ => []
  | k + 1, r => digitsExactly k (r / 10) ++ [(r % 10).digitChar]

def exactDigitsFast (k r : Nat) : List Char :=
  if k ≤ 64 then digitsExactly k r
  else exactDigitsFast (k - k / 2) (r / 10 ^ (k / 2)) ++ exactDigitsFast (k / 2) (r % 10 ^ (k / 2))
termination_by k
decreasing_by all_goals omega

def toDigitsFast (n : Nat) : List Char :=
  if n < 10 ^ 64 then Nat.toDigits 10 n
  else toDigitsFast (n / 10 ^ (n.log2 / 8)) ++ exactDigitsFast (n.log2 / 8) (n % 10 ^ (n.log2 / 8))
termination_by n
decreasing_by
  have hlog : 212 ≤ n.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
  exact Nat.div_lt_self (by omega) (Nat.one_lt_pow (by omega) (by decide))

theorem digitsExactly_mod : ∀ (b r : Nat), digitsExactly b (r % 10 ^ b) = digitsExactly b r
  | 0, _ => rfl
  | b + 1, r => by
    simp only [digitsExactly]
    rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul_right_div_self, digitsExactly_mod b (r / 10),
      Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right 10 _)]

theorem digitsExactly_add : ∀ (a b r : Nat), digitsExactly (a + b) r = digitsExactly a (r / 10 ^ b) ++ digitsExactly b r
  | a, 0, r => by simp [digitsExactly]
  | a, b + 1, r => by
    rw [← Nat.add_assoc]
    simp only [digitsExactly]
    rw [digitsExactly_add a b (r / 10), Nat.div_div_eq_div_mul, ← Nat.pow_succ', List.append_assoc]

theorem exactDigitsFast_eq : ∀ (k r : Nat), exactDigitsFast k r = digitsExactly k r := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro r
    rw [exactDigitsFast]
    split
    · rfl
    · rw [ih _ (by omega), ih _ (by omega), digitsExactly_mod]
      conv => rhs; rw [show k = (k - k / 2) + k / 2 by omega]
      rw [digitsExactly_add]

theorem toDigits_split : ∀ (k q r : Nat), 0 < q → r < 10 ^ k →
    Nat.toDigits 10 (q * 10 ^ k + r) = Nat.toDigits 10 q ++ digitsExactly k r
  | 0, q, r, _, hr => by
    have : r = 0 := by simpa using hr
    subst this
    simp [digitsExactly]
  | k + 1, q, r, hq, hr => by
    have hn : ¬ q * 10 ^ (k + 1) + r < 10 := by
      have : 10 ≤ q * 10 ^ (k + 1) := by
        calc 10 ≤ 10 ^ (k + 1) := Nat.le_self_pow (by omega) _
          _ ≤ q * 10 ^ (k + 1) := Nat.le_mul_of_pos_left _ hq
      omega
    rw [Nat.toDigits_eq_ite (by decide), ite_eq_right hn]
    have hdiv : (q * 10 ^ (k + 1) + r) / 10 = q * 10 ^ k + r / 10 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      omega
    have hmod : (q * 10 ^ (k + 1) + r) % 10 = r % 10 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
      omega
    rw [hdiv, hmod, toDigits_split k q (r / 10) hq (by rw [Nat.pow_succ] at hr; omega)]
    simp only [digitsExactly, List.append_assoc]

theorem toDigitsFast_eq : ∀ (n : Nat), toDigitsFast n = Nat.toDigits 10 n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [toDigitsFast]
    split
    · rfl
    · rename_i h
      have hlog : 212 ≤ n.log2 := (Nat.le_log2 (by omega)).mpr (by omega)
      have hp : 10 ^ (n.log2 / 8) ≤ n := by
        calc 10 ^ (n.log2 / 8) ≤ 16 ^ (n.log2 / 8) := Nat.pow_le_pow_left (by decide) _
          _ = 2 ^ (4 * (n.log2 / 8)) := by rw [Nat.pow_mul]
          _ ≤ 2 ^ n.log2 := Nat.pow_le_pow_right (by decide) (by omega)
          _ ≤ n := Nat.log2_self_le (by omega)
      have hq : 0 < n / 10 ^ (n.log2 / 8) := Nat.div_pos hp (Nat.pow_pos (by decide))
      rw [ih _ (Nat.div_lt_self (by omega) (Nat.one_lt_pow (by omega) (by decide))), exactDigitsFast_eq,
        ← toDigits_split _ _ _ hq (Nat.mod_lt _ (Nat.pow_pos (by decide))), Nat.mul_comm, Nat.div_add_mod]

def intText (n : Int) : String :=
  if 0 ≤ n then String.ofList (toDigitsFast n.toNat) else "-" ++ String.ofList (toDigitsFast (-n).toNat)

theorem intText_eq (n : Int) : intText n = toString n := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  unfold intText
  have h : ∀ m : Nat, String.ofList (toDigitsFast m) = m.repr := fun m =>
    String.toList_inj.mp (by rw [String.toList_ofList, Nat.toList_repr, toDigitsFast_eq])
  split
  · exact h _
  · rw [h]

def decimalTextFast (d : Decimal) : String :=
  let sign : List Char := if d.negative then ['-'] else []
  if d.digits = 0 then String.ofList (sign ++ "0.0".toList)
  else
    let ds := toDigitsFast d.digits
    let n := ds.length
    let sci : Int := d.exponent + n - 1
    let body : List Char :=
      if -4 ≤ sci ∧ sci < 16 then
        if sci ≥ n - 1 then ds ++ Decimal.zeros (sci - (n - 1) : Int).toNat ++ ['.', '0']
        else if 0 ≤ sci then ds.take (sci.toNat + 1) ++ ['.'] ++ ds.drop (sci.toNat + 1)
        else ['0', '.'] ++ Decimal.zeros ((-sci).toNat - 1) ++ ds
      else
        ds.take 1 ++ ['.'] ++ (if n = 1 then ['0'] else ds.drop 1) ++ ['e'] ++ (intText sci).toList
    String.ofList (sign ++ body)

theorem decimalTextFast_eq (d : Decimal) : decimalTextFast d = d.text := by
  unfold decimalTextFast Decimal.text
  simp only [toDigitsFast_eq, intText_eq]

@[csimp] theorem decimalText_eq_fast : @Decimal.text = @decimalTextFast := by
  funext d
  exact (decimalTextFast_eq d).symm

end ExactJSON
