module

public import ExactJSON.ReadBack

public section

namespace ExactJSON.FloatText

open Float.Model Float.Model.UnpackedFloat

def Represents (em : ExtendedMantissa) (N D : Nat) : Prop :=
  em.mantissa = N / D ∧ em.roundBit = decide (D ≤ 2 * (N % D)) ∧
    em.stickyBit = decide (N % D ≠ 0 ∧ 2 * (N % D) ≠ D)

theorem represents_shiftRightOne {em : ExtendedMantissa} {N D : Nat} (hD : 0 < D) (h : Represents em N D) :
    Represents em.shiftRightOne N (D * 2) := by
  obtain ⟨hm, hr, hs⟩ := h
  have hR := Nat.mod_lt N hD
  have hmod : N % (D * 2) = N % D + D * (N / D % 2) := Nat.mod_mul
  simp only [ExtendedMantissa.shiftRightOne]
  refine ⟨by rw [hm]; exact Nat.div_div_eq_div_mul N D 2, ?_, ?_⟩
  · rw [hm]
    apply Bool.eq_iff_iff.mpr
    rcases (by omega : N / D % 2 = 0 ∨ N / D % 2 = 1) with hb | hb <;>
      simp only [hb, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hmod <;>
      simp only [hb, hmod, bne_iff_ne, ne_eq, decide_eq_true_eq, not_true_eq_false, false_iff,
        Nat.one_ne_zero, not_false_eq_true, true_iff, Nat.not_le] <;> omega
  · rw [hr, hs]
    apply Bool.eq_iff_iff.mpr
    rcases (by omega : N / D % 2 = 0 ∨ N / D % 2 = 1) with hb | hb <;>
      simp only [hb, Nat.mul_zero, Nat.mul_one, Nat.add_zero] at hmod <;>
      simp only [hmod, Bool.or_eq_true, decide_eq_true_eq] <;> omega

theorem represents_shift {em : ExtendedMantissa} {N D : Nat} (hD : 0 < D) (h : Represents em N D) :
    ∀ n : Nat, Represents (em >>> n) N (D * 2 ^ n)
  | 0 => by
    have : em >>> 0 = em := rfl
    rw [this, Nat.pow_zero, Nat.mul_one]
    exact h
  | n + 1 => by
    have ih := represents_shift hD h n
    have : em >>> (n + 1) = (em >>> n).shiftRightOne := rfl
    rw [this, Nat.pow_succ, ← Nat.mul_assoc]
    exact represents_shiftRightOne (Nat.mul_pos hD (Nat.pow_pos (by decide))) ih

theorem represents_ofMantissaAndAccuracy (N D : Nat) (hD : 0 < D) :
    Represents (ExtendedMantissa.ofMantissaAndAccuracy (N / D) (accuracyOfFraction (N % D) D)) N D := by
  have hR := Nat.mod_lt N hD
  unfold accuracyOfFraction
  by_cases h0 : N % D = 0
  · simp only [h0, ite_true]
    refine ⟨rfl, ?_, ?_⟩ <;> simp [ExtendedMantissa.ofMantissaAndAccuracy, h0] <;> omega
  · simp only [h0, ite_false]
    rcases Nat.lt_trichotomy (2 * (N % D)) D with hc | hc | hc
    · rw [(Nat.compare_eq_lt).mpr hc]
      refine ⟨rfl, ?_, ?_⟩ <;> simp [ExtendedMantissa.ofMantissaAndAccuracy] <;> omega
    · rw [(Nat.compare_eq_eq).mpr hc]
      refine ⟨rfl, ?_, ?_⟩ <;> simp [ExtendedMantissa.ofMantissaAndAccuracy] <;> omega
    · rw [(Nat.compare_eq_gt).mpr hc]
      refine ⟨rfl, ?_, ?_⟩ <;> simp [ExtendedMantissa.ofMantissaAndAccuracy] <;> omega

theorem represents_exact (a : Nat) : Represents (ExtendedMantissa.ofMantissaAndAccuracy a .exact) a 1 := by
  refine ⟨by simp [ExtendedMantissa.ofMantissaAndAccuracy], ?_, ?_⟩ <;>
    simp [ExtendedMantissa.ofMantissaAndAccuracy, Nat.mod_one]

theorem roundedMantissa_eq {em : ExtendedMantissa} {N D : Nat} (hD : 0 < D) (h : Represents em N D) :
    em.roundedMantissa =
      if 2 * (N % D) < D then N / D else if 2 * (N % D) = D then N / D + N / D % 2 else N / D + 1 := by
  obtain ⟨hm, hr, hs⟩ := h
  rcases em with ⟨a, r, s⟩
  simp only at hm hr hs
  subst hm
  unfold ExtendedMantissa.roundedMantissa
  have hr' := congrArg (· = true) hr
  have hs' := congrArg (· = true) hs
  simp only [decide_eq_true_eq, eq_iff_iff] at hr' hs'
  cases r <;> cases s <;> simp only [ExtendedMantissa.accuracy, Accuracy.roundToNearestEven] <;>
    simp only [Bool.false_eq_true, false_iff, true_iff, ne_eq, Nat.not_le, not_and, Decidable.not_not] at hr' hs'
  · rw [ite_eq_left (by omega)]
  · rw [ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem roundedMantissa_of_near {em : ExtendedMantissa} {N D M : Nat} (hD : 0 < D) (h : Represents em N D)
    (incl : Bool) (hincl : incl = true → M % 2 = 0)
    (hlo : 2 * (M * D) < 2 * N + D ∨ (incl = true ∧ 2 * (M * D) = 2 * N + D))
    (hhi : 2 * N < 2 * (M * D) + D ∨ (incl = true ∧ 2 * N = 2 * (M * D) + D)) :
    em.roundedMantissa = M := by
  rw [roundedMantissa_eq hD h]
  have hN := Nat.div_add_mod N D
  have hR := Nat.mod_lt N hD
  generalize N / D = a at hN ⊢
  generalize N % D = R at hN hR ⊢
  subst hN
  rw [Nat.mul_comm D a] at hlo hhi
  have h1 : M ≤ a + 1 := by
    have : 2 * M * D < (2 * a + 3) * D := by
      rw [Nat.mul_assoc, Nat.add_mul, Nat.mul_assoc]; omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  have h2 : a ≤ M := by
    have : 2 * a * D < (2 * M + 2) * D := by
      rw [Nat.mul_assoc, Nat.add_mul, Nat.mul_assoc]; omega
    have := Nat.lt_of_mul_lt_mul_right this
    omega
  rcases (by omega : a = M ∨ a + 1 = M) with rfl | rfl
  · by_cases c1 : 2 * R < D
    · rw [ite_eq_left c1]
    · have c2 : 2 * R = D := by omega
      rw [ite_eq_right c1, ite_eq_left c2]
      rcases hhi with hhi | ⟨hi, -⟩
      · omega
      · have := hincl hi
        omega
  · rw [Nat.add_mul, Nat.one_mul] at hlo hhi
    have c1 : ¬ 2 * R < D := by omega
    by_cases c2 : 2 * R = D
    · rw [ite_eq_right c1, ite_eq_left c2]
      rcases hlo with hlo | ⟨hi, -⟩
      · omega
      · have := hincl hi
        omega
    · rw [ite_eq_right c1, ite_eq_right c2]

theorem two_pow_mul_powSplit_lt_iff (L K : Nat) (d : Int) :
    2 ^ L * (powSplit 2 d).1 < 2 ^ K * (powSplit 2 d).2 ↔ (L : Int) + d < K := by
  unfold powSplit
  by_cases hd : 0 ≤ d
  · simp only [hd, ite_true, Nat.mul_one]
    rw [← Nat.pow_add, Nat.pow_lt_pow_iff_right (by decide)]
    omega
  · simp only [hd, ite_false, Nat.mul_one]
    rw [← Nat.pow_add, Nat.pow_lt_pow_iff_right (by decide)]
    omega

theorem two_pow_mul_powSplit_lt_iff' (L K : Nat) (d : Int) :
    2 ^ K * (powSplit 2 d).2 < 2 ^ L * (powSplit 2 d).1 ↔ (K : Int) < L + d := by
  unfold powSplit
  by_cases hd : 0 ≤ d
  · simp only [hd, ite_true, Nat.mul_one]
    rw [← Nat.pow_add, Nat.pow_lt_pow_iff_right (by decide)]
    omega
  · simp only [hd, ite_false, Nat.mul_one]
    rw [← Nat.pow_add, Nat.pow_lt_pow_iff_right (by decide)]
    omega

theorem powSplit_two_shift (k s : Nat) :
    (powSplit 2 ((k : Int) - s)).1 * 2 ^ s = 2 ^ k * (powSplit 2 ((k : Int) - s)).2 := by
  unfold powSplit
  by_cases hd : 0 ≤ (k : Int) - s
  · simp only [hd, ite_true, Nat.mul_one]
    rw [← Nat.pow_add]
    congr 1
    omega
  · simp only [hd, ite_false, Nat.one_mul]
    rw [← Nat.pow_add]
    congr 1
    omega

theorem transport {P Q K D : Nat} (hQ : 0 < Q) (hDp : 0 < D) (h : P * D = K * Q) (c : Nat) :
    (c * Q < P ↔ c * D < K) ∧ (P < c * Q ↔ K < c * D) ∧ (c * Q = P ↔ c * D = K) ∧
      (c * Q ≤ P ↔ c * D ≤ K) := by
  have key : ∀ y : Nat, y * Q * D = y * D * Q := fun y => by ac_rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Nat.mul_lt_mul_right hDp, h, key, Nat.mul_lt_mul_right hQ]
  · rw [← Nat.mul_lt_mul_right hDp, h, key, Nat.mul_lt_mul_right hQ]
  · constructor
    · intro h1
      have : c * Q * D = P * D := by rw [h1]
      rw [h, key] at this
      exact Nat.eq_of_mul_eq_mul_right hQ this
    · intro h1
      have : c * D * Q = K * Q := by rw [h1]
      rw [← h, ← key] at this
      exact Nat.eq_of_mul_eq_mul_right hDp this
  · rw [← Nat.mul_le_mul_right_iff hDp, h, key, Nat.mul_le_mul_right_iff hQ]

theorem fits_iff (low high Q : Nat) (incl : Bool) (P : Nat) :
    fits low high Q 1 incl P = true ↔
      (low * Q < P ∨ (incl = true ∧ low * Q = P)) ∧ (P < high * Q ∨ (incl = true ∧ P = high * Q)) := by
  unfold fits
  simp only [Nat.mul_one, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]

theorem ofMantissaAndAccuracy_mantissa (m : Nat) (a : Accuracy) :
    (ExtendedMantissa.ofMantissaAndAccuracy m a).mantissa = m := by
  cases a with
  | exact => rfl
  | inexact o => cases o <;> rfl

theorem targetExponent_binary64 (t : Int) : Format.binary64.targetExponent t = max (t - 53) (-1074) := by
  simp [Format.targetExponent, Format.mantissaBits, Format.minExponent]

theorem finite_of_eq (sg : Sign) {X M : Nat} {Y e : Int} (hX : X = M) (hY : Y = e) (hM0 : M ≠ 0) :
    (if h : X = 0 then UnpackedFloat.zero sg else .finite sg X Y (Nat.pos_of_ne_zero h)) =
      .finite sg M e (Nat.pos_of_ne_zero hM0) := by
  subst hX hY
  simp [hM0]

theorem round_at_exponent {em : ExtendedMantissa} {N D Pw Qw M : Nat} (incl : Bool) (hD : 0 < D) (hQw : 0 < Qw)
    (hM : 0 < M) (hrep : Represents em N D) (hglue : Pw * D = 4 * N * Qw) (hincl : incl = true → M % 2 = 0)
    (hlo : (4 * M - 2) * Qw < Pw ∨ (incl = true ∧ (4 * M - 2) * Qw = Pw) ∨ 4 * M * Qw ≤ Pw)
    (hhi : Pw < (4 * M + 2) * Qw ∨ (incl = true ∧ Pw = (4 * M + 2) * Qw)) :
    em.roundedMantissa = M := by
  have tr := transport hQw hD hglue
  have hX : ∀ c : Nat, c * M * D = c * (M * D) := fun c => Nat.mul_assoc c M D
  have hMD : D ≤ M * D := Nat.le_mul_of_pos_left D hM
  apply roundedMantissa_of_near hD hrep incl hincl
  · rcases hlo with h | ⟨hi, h⟩ | h
    · have h1 := (tr (4 * M - 2)).1.mp h
      rw [Nat.sub_mul, hX] at h1
      left; omega
    · have h1 := (tr (4 * M - 2)).2.2.1.mp h
      rw [Nat.sub_mul, hX] at h1
      right; exact ⟨hi, by omega⟩
    · have h1 := (tr (4 * M)).2.2.2.mp h
      rw [hX] at h1
      left; omega
  · rcases hhi with h | ⟨hi, h⟩
    · have h1 := (tr (4 * M + 2)).2.1.mp h
      rw [Nat.add_mul, hX] at h1
      left; omega
    · have h1 := (tr (4 * M + 2)).2.2.1.mp h.symm
      rw [Nat.add_mul, hX] at h1
      right; exact ⟨hi, by omega⟩

theorem round_below_power {em : ExtendedMantissa} {N D Pw Qw : Nat} (hD : 0 < D) (hQw : 0 < Qw)
    (hrep : Represents em N D) (hglue : Pw * D = 2 * N * Qw)
    (hlo : (2 ^ 54 - 1) * Qw ≤ Pw) (hhi : Pw < 2 ^ 54 * Qw) :
    em.roundedMantissa = 2 ^ 53 := by
  have tr := transport hQw hD hglue
  have h1 := (tr (2 ^ 54 - 1)).2.2.2.mp hlo
  have h2 := (tr (2 ^ 54)).2.1.mp hhi
  have e1 : (2 ^ 54 - 1) * D = 2 * (2 ^ 53 * D) - D := by
    rw [Nat.sub_mul, Nat.one_mul, ← Nat.mul_assoc]
  have e2 : 2 ^ 54 * D = 2 * (2 ^ 53 * D) := by
    rw [← Nat.mul_assoc]
  rw [e1] at h1
  rw [e2] at h2
  apply roundedMantissa_of_near hD hrep true (fun _ => by decide)
  · generalize 2 ^ 53 * D = X at h1 h2 ⊢
    by_cases h : 2 * X < 2 * N + D
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩
  · generalize 2 ^ 53 * D = X at h1 h2 ⊢
    exact Or.inl (by omega)

theorem roundWithAccuracy_eq (sg : Sign) {M : Nat} {e : Int} (hM0 : M ≠ 0) (hM : M < 2 ^ 53)
    (he : -1074 ≤ e) (hsub : M < 2 ^ 52 → e = -1074)
    {mant : Nat} {ex : Int} {acc : Accuracy} {N D : Nat} (hD : 0 < D)
    (hrep : Represents (ExtendedMantissa.ofMantissaAndAccuracy mant acc) N D)
    (hprec : 52 ≤ mant.log2 ∨ ex ≤ -1074)
    {Pw Qw : Nat} (hQw : 0 < Qw)
    (hglue : Pw * (D * (powSplit 2 (ex - (e - 2))).2) = N * (powSplit 2 (ex - (e - 2))).1 * Qw)
    (hint : fits (roundingInterval M (decide (M = 2 ^ 52) && decide (e > -1074))).1
      (roundingInterval M (decide (M = 2 ^ 52) && decide (e > -1074))).2.2 Qw 1 (M % 2 == 0) Pw = true) :
    roundWithAccuracy Format.binary64 sg mant ex acc = .finite sg M e (Nat.pos_of_ne_zero hM0) := by
  have hmant : mant = N / D := by
    have := hrep.1
    rwa [ofMantissaAndAccuracy_mantissa] at this
  rw [fits_iff] at hint
  obtain ⟨hlo, hhi⟩ := hint
  have hw := powSplit_pos 2 (by decide) (ex - (e - 2))
  generalize hd : ex - (e - 2) = d at hglue hw
  generalize hL : mant.log2 = L at hprec
  have hW2 : Pw * (powSplit 2 d).2 < 2 ^ (L + 1) * (powSplit 2 d).1 * Qw := by
    have h1 : N < 2 ^ (L + 1) * D := by
      have h0 := Nat.div_add_mod N D
      have h0' := Nat.mod_lt N hD
      have h2 : mant < 2 ^ (L + 1) := hL ▸ Nat.lt_log2_self
      rw [hmant] at h2
      have h3 : N < D * (N / D + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      calc N < D * (N / D + 1) := h3
        _ ≤ D * 2 ^ (L + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = 2 ^ (L + 1) * D := Nat.mul_comm _ _
    have : Pw * (powSplit 2 d).2 * D < 2 ^ (L + 1) * (powSplit 2 d).1 * Qw * D := by
      calc Pw * (powSplit 2 d).2 * D = N * (powSplit 2 d).1 * Qw := by rw [← hglue]; ac_rfl
        _ < 2 ^ (L + 1) * D * (powSplit 2 d).1 * Qw := by
          apply Nat.mul_lt_mul_of_pos_right _ hQw
          exact Nat.mul_lt_mul_of_pos_right h1 hw.1
        _ = 2 ^ (L + 1) * (powSplit 2 d).1 * Qw * D := by ac_rfl
    exact Nat.lt_of_mul_lt_mul_right this
  have hW1 : mant ≠ 0 → 2 ^ L * (powSplit 2 d).1 * Qw ≤ Pw * (powSplit 2 d).2 := by
    intro hm0
    have h1 : 2 ^ L * D ≤ N := by
      have h2 : 2 ^ L ≤ mant := hL ▸ Nat.log2_self_le hm0
      rw [hmant] at h2
      calc 2 ^ L * D ≤ N / D * D := Nat.mul_le_mul_right _ h2
        _ ≤ N := Nat.div_mul_le_self N D
    have : 2 ^ L * (powSplit 2 d).1 * Qw * D ≤ Pw * (powSplit 2 d).2 * D := by
      calc 2 ^ L * (powSplit 2 d).1 * Qw * D = 2 ^ L * D * (powSplit 2 d).1 * Qw := by ac_rfl
        _ ≤ N * (powSplit 2 d).1 * Qw := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ h1)
        _ = Pw * (powSplit 2 d).2 * D := by rw [← hglue]; ac_rfl
    exact Nat.le_of_mul_le_mul_right this hD
  have below : ∀ K : Nat, mant ≠ 0 → Pw < 2 ^ K * Qw → (L : Int) + d < K := by
    intro K hm0 hK
    have h1 := hW1 hm0
    have h2 : Pw * (powSplit 2 d).2 < 2 ^ K * Qw * (powSplit 2 d).2 := Nat.mul_lt_mul_of_pos_right hK hw.2
    have : 2 ^ L * (powSplit 2 d).1 * Qw < 2 ^ K * (powSplit 2 d).2 * Qw := by
      calc 2 ^ L * (powSplit 2 d).1 * Qw ≤ Pw * (powSplit 2 d).2 := h1
        _ < 2 ^ K * Qw * (powSplit 2 d).2 := h2
        _ = 2 ^ K * (powSplit 2 d).2 * Qw := by ac_rfl
    exact (two_pow_mul_powSplit_lt_iff L K d).mp (Nat.lt_of_mul_lt_mul_right this)
  have above : ∀ K : Nat, 2 ^ K * Qw ≤ Pw → (K : Int) < L + 1 + d := by
    intro K hK
    have h2 : 2 ^ K * Qw * (powSplit 2 d).2 ≤ Pw * (powSplit 2 d).2 := Nat.mul_le_mul_right _ hK
    have : 2 ^ K * (powSplit 2 d).2 * Qw < 2 ^ (L + 1) * (powSplit 2 d).1 * Qw := by
      calc 2 ^ K * (powSplit 2 d).2 * Qw = 2 ^ K * Qw * (powSplit 2 d).2 := by ac_rfl
        _ ≤ Pw * (powSplit 2 d).2 := h2
        _ < 2 ^ (L + 1) * (powSplit 2 d).1 * Qw := hW2
    have := (two_pow_mul_powSplit_lt_iff' (L + 1) K d).mp (Nat.lt_of_mul_lt_mul_right this)
    push_cast at this
    exact this
  simp only [roundingInterval] at hlo hhi
  have hPw55 : Pw < 2 ^ 55 * Qw := by
    have : (4 * M + 2) * Qw < 2 ^ 55 * Qw := Nat.mul_lt_mul_of_pos_right (by omega) hQw
    rcases hhi with h | ⟨-, h⟩ <;> omega
  have hTle : max ((L : Int) + 1 + ex - 53) (-1074) ≤ e := by
    by_cases hm0 : mant = 0
    · have : L = 0 := by rw [← hL, hm0]; rfl
      rcases hprec with h | h <;> omega
    · have := below 55 hm0 hPw55
      omega
  have hTex : ex ≤ max ((L : Int) + 1 + ex - 53) (-1074) := by omega
  have hlogM : M.log2 < 53 := (Nat.log2_lt hM0).mpr hM
  have hincl : (M % 2 == 0) = true → M % 2 = 0 := fun h => by simpa using h
  unfold roundWithAccuracy shiftToTargetExponent shiftToExponent
  simp only [targetExponent_binary64, totalExponent, hL]
  by_cases hA : e = -1074 ∨ 2 ^ 54 * Qw ≤ Pw
  · have hT : max ((L : Int) + 1 + ex - 53) (-1074) = e := by
      rcases hA with h | h
      · omega
      · have := above 54 h
        omega
    obtain ⟨s, hs⟩ : ∃ s, (e - ex).toNat = s := ⟨_, rfl⟩
    have hs' : (s : Int) = e - ex := by omega
    have hrep1 := represents_shift hD hrep s
    have hD' : 0 < D * 2 ^ s := Nat.mul_pos hD (Nat.pow_pos (by decide))
    have hglueT : Pw * (D * 2 ^ s) = 4 * N * Qw := by
      have hd' : d = ((2 : Nat) : Int) - (s : Int) := by omega
      rw [hd'] at hglue hw
      have hsh := powSplit_two_shift 2 s
      apply Nat.eq_of_mul_eq_mul_right hw.2
      calc Pw * (D * 2 ^ s) * (powSplit 2 ((2 : Nat) - (s : Int))).2
          = Pw * (D * (powSplit 2 ((2 : Nat) - (s : Int))).2) * 2 ^ s := by ac_rfl
        _ = N * (powSplit 2 ((2 : Nat) - (s : Int))).1 * Qw * 2 ^ s := by rw [hglue]
        _ = N * Qw * ((powSplit 2 ((2 : Nat) - (s : Int))).1 * 2 ^ s) := by ac_rfl
        _ = N * Qw * (2 ^ 2 * (powSplit 2 ((2 : Nat) - (s : Int))).2) := by rw [hsh]
        _ = 4 * N * Qw * (powSplit 2 ((2 : Nat) - (s : Int))).2 := by
          rw [show (2 : Nat) ^ 2 = 4 from rfl]; ac_rfl
    have hround : (ExtendedMantissa.ofMantissaAndAccuracy mant acc >>> s).roundedMantissa = M := by
      apply round_at_exponent (M % 2 == 0) hD' hQw (Nat.pos_of_ne_zero hM0) hrep1 hglueT hincl _ hhi
      by_cases hlc : M = 2 ^ 52 ∧ e > -1074
      · right; right
        have h54 : 2 ^ 54 * Qw ≤ Pw := by omega
        rw [hlc.1, show 4 * 2 ^ 52 = 2 ^ 54 by decide]
        exact h54
      · have hl : (decide (M = 2 ^ 52) && decide (e > -1074)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        rw [hl] at hlo
        simp only [Bool.false_eq_true, ite_false] at hlo
        rcases hlo with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
    have h0 : (max ((M.log2 : Int) + 1 + (ex + s) - 53) (-1074) - (ex + s)).toNat = 0 := by omega
    simp only [hT, hs, hround, h0]
    refine finite_of_eq sg ?_ ?_ hM0
    · rfl
    · omega
  · have he' : e ≠ -1074 := fun h => hA (Or.inl h)
    have hPw : Pw < 2 ^ 54 * Qw := by omega
    have hM52 : M = 2 ^ 52 := by
      have : 2 ^ 52 ≤ M := by
        by_cases h : M < 2 ^ 52
        · exact absurd (hsub h) he'
        · omega
      by_cases h : M = 2 ^ 52
      · exact h
      · have hl : (decide (M = 2 ^ 52) && decide (e > -1074)) = false := by
          simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
          omega
        rw [hl] at hlo
        simp only [Bool.false_eq_true, ite_false] at hlo
        have : (2 ^ 54 + 2) * Qw ≤ (4 * M - 2) * Qw := Nat.mul_le_mul_right _ (by omega)
        rcases hlo with h | ⟨-, h⟩ <;> omega
    have hl : (decide (M = 2 ^ 52) && decide (e > -1074)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    rw [hl] at hlo
    simp only [ite_true] at hlo
    have hlo' : (2 ^ 54 - 1) * Qw ≤ Pw := by
      rw [show (2 : Nat) ^ 54 - 1 = 4 * M - 1 by rw [hM52]]
      rcases hlo with h | ⟨-, h⟩
      · exact Nat.le_of_lt h
      · exact Nat.le_of_eq h
    have hT : max ((L : Int) + 1 + ex - 53) (-1074) = e - 1 := by
      have h53 : 2 ^ 53 * Qw ≤ Pw :=
        Nat.le_trans (Nat.mul_le_mul_right _ (by decide : 2 ^ 53 ≤ 2 ^ 54 - 1)) hlo'
      have := above 53 h53
      by_cases hm0 : mant = 0
      · have : L = 0 := by rw [← hL, hm0]; rfl
        rcases hprec with h | h <;> omega
      · have := below 54 hm0 hPw
        omega
    obtain ⟨s, hs⟩ : ∃ s, (e - 1 - ex).toNat = s := ⟨_, rfl⟩
    have hs' : (s : Int) = e - 1 - ex := by omega
    have hrep1 := represents_shift hD hrep s
    have hD' : 0 < D * 2 ^ s := Nat.mul_pos hD (Nat.pow_pos (by decide))
    have hglueT : Pw * (D * 2 ^ s) = 2 * N * Qw := by
      have hd' : d = ((1 : Nat) : Int) - (s : Int) := by omega
      rw [hd'] at hglue hw
      have hsh := powSplit_two_shift 1 s
      apply Nat.eq_of_mul_eq_mul_right hw.2
      calc Pw * (D * 2 ^ s) * (powSplit 2 ((1 : Nat) - (s : Int))).2
          = Pw * (D * (powSplit 2 ((1 : Nat) - (s : Int))).2) * 2 ^ s := by ac_rfl
        _ = N * (powSplit 2 ((1 : Nat) - (s : Int))).1 * Qw * 2 ^ s := by rw [hglue]
        _ = N * Qw * ((powSplit 2 ((1 : Nat) - (s : Int))).1 * 2 ^ s) := by ac_rfl
        _ = N * Qw * (2 ^ 1 * (powSplit 2 ((1 : Nat) - (s : Int))).2) := by rw [hsh]
        _ = 2 * N * Qw * (powSplit 2 ((1 : Nat) - (s : Int))).2 := by rw [Nat.pow_one]; ac_rfl
    have hround : (ExtendedMantissa.ofMantissaAndAccuracy mant acc >>> s).roundedMantissa = 2 ^ 53 :=
      round_below_power hD' hQw hrep1 hglueT hlo' hPw
    have h1 : (max (((2 ^ 53 : Nat).log2 : Int) + 1 + (ex + s) - 53) (-1074) - (ex + s)).toNat = 1 := by
      rw [Nat.log2_two_pow]
      omega
    simp only [hT, hs, hround, h1]
    refine finite_of_eq sg ?_ ?_ hM0
    · rw [hM52]
      show 2 ^ 53 / 2 = 2 ^ 52
      decide
    · omega

theorem pack_normal (m : Nat) (e : Int) (h : 0 < m) (hm1 : 2 ^ 52 ≤ m) (hm2 : m < 2 ^ 53) (he1 : -1074 ≤ e)
    (he2 : e ≤ 971) :
    (UnpackedFloat.pack Format.binary64 (.finite .positive m e h)).toNat =
      (e + 1075).toNat * 2 ^ 52 + (m - 2 ^ 52) := by
  have hlog : m.log2 = 52 := by
    have h1 := (Nat.le_log2 (n := m) (by omega)).mpr hm1
    have h2 := (Nat.log2_lt (n := m) (by omega)).mpr hm2
    omega
  unfold UnpackedFloat.pack
  dsimp only
  split
  · rename_i hc
    simp only [Format.exponentBias] at hc
    omega
  · split
    · rw [packComponents_toNat]
      simp only [Sign.toBitVec, BitVec.toNat_ofNat, Format.exponentBias]
      omega
    · rename_i hc
      simp [Format.mantissaBits, hlog] at hc

theorem pack_subnormal (m : Nat) (h : 0 < m) (hm : m < 2 ^ 52) :
    (UnpackedFloat.pack Format.binary64 (.finite .positive m (-1074) h)).toNat = m := by
  have hlog : m.log2 < 52 := (Nat.log2_lt (by omega)).mpr hm
  unfold UnpackedFloat.pack
  dsimp only
  split
  · rename_i hc
    simp only [Format.exponentBias] at hc
    omega
  · split
    · rename_i hc
      simp only [Format.mantissaBits] at hc
      omega
    · rw [packComponents_toNat]
      simp only [Sign.toBitVec, BitVec.toNat_ofNat]
      omega

theorem pack_decompose {x : Float} (hx : finiteFloat x = true) {M : Nat} {e : Int}
    (hd : decompose x = (false, M, e)) (hM : 0 < M) :
    UnpackedFloat.pack Format.binary64 (.finite .positive M e hM) = x.toBits.toBitVec := by
  apply BitVec.eq_of_toNat_eq
  have hlt := x.toBits.toNat_lt
  unfold finiteFloat at hx
  simp only [bne_iff_ne, ne_eq] at hx
  unfold decompose at hd
  simp only at hd
  split at hd
  · rename_i h0
    simp only [Prod.mk.injEq, decide_eq_false_iff_not] at hd
    obtain ⟨hs, rfl, rfl⟩ := hd
    rw [pack_subnormal _ _ (Nat.mod_lt _ (by decide)), UInt64.toNat_toBitVec]
    omega
  · rename_i h0
    simp only [Prod.mk.injEq, decide_eq_false_iff_not] at hd
    obtain ⟨hs, rfl, rfl⟩ := hd
    rw [pack_normal _ _ _ (by omega) (by omega) (by omega) (by omega), UInt64.toNat_toBitVec]
    omega

theorem divCore_spec (m₁ m₂ : Nat) (e₁ e₂ : Int) (h₁ : 0 < m₁) (h₂ : 0 < m₂) :
    ∃ sh : Nat, divCore Format.binary64 m₁ e₁ m₂ e₂ =
      ((m₁ * 2 ^ sh) / m₂, e₁ - e₂ - sh, accuracyOfFraction ((m₁ * 2 ^ sh) % m₂) m₂) ∧
      (52 ≤ ((m₁ * 2 ^ sh) / m₂).log2 ∨ e₁ - e₂ - sh ≤ -1074) := by
  unfold divCore
  simp only [targetExponent_binary64, totalExponent, Nat.shiftLeft_eq]
  generalize hT : min (e₁ - e₂) (max ((m₁.log2 : Int) + 1 + e₁ - ((m₂.log2 : Int) + 1 + e₂) - 53) (-1074)) = T
  have hTle : T ≤ e₁ - e₂ := by omega
  refine ⟨(e₁ - e₂ - T).toNat, ?_, ?_⟩
  · have : e₁ - e₂ - (((e₁ - e₂ - T).toNat : Nat) : Int) = T := by omega
    rw [this]
  · by_cases hlow : T ≤ -1074
    · right; omega
    · left
      generalize hsh : (e₁ - e₂ - T).toNat = sh
      have hsh' : (sh : Int) = e₁ - e₂ - T := by omega
      have hL1 := Nat.log2_self_le (Nat.pos_iff_ne_zero.mp h₁)
      have hL2 : m₂ < 2 ^ (m₂.log2 + 1) := Nat.lt_log2_self
      have hge : m₂.log2 + 53 ≤ m₁.log2 + sh := by omega
      have key : 2 ^ 52 * m₂ ≤ m₁ * 2 ^ sh := by
        calc 2 ^ 52 * m₂ ≤ 2 ^ 52 * 2 ^ (m₂.log2 + 1) := Nat.mul_le_mul_left _ (Nat.le_of_lt hL2)
          _ = 2 ^ (m₂.log2 + 53) := by rw [← Nat.pow_add]; congr 1; omega
          _ ≤ 2 ^ (m₁.log2 + sh) := Nat.pow_le_pow_right (by decide) hge
          _ = 2 ^ m₁.log2 * 2 ^ sh := Nat.pow_add _ _ _
          _ ≤ m₁ * 2 ^ sh := Nat.mul_le_mul_right _ hL1
      have hq : 2 ^ 52 ≤ (m₁ * 2 ^ sh) / m₂ := (Nat.le_div_iff_mul_le h₂).mpr key
      exact (Nat.le_log2 (by omega)).mpr hq

theorem unpack_normal (b : BitVec 64) (h1 : b.toNat / 2 ^ 52 % 2 ^ 11 ≠ 0) (h2 : b.toNat / 2 ^ 52 % 2 ^ 11 ≠ 2047)
    (hs : b.toNat < 2 ^ 63) :
    UnpackedFloat.unpack Format.binary64 b =
      .finite .positive (2 ^ 52 + b.toNat % 2 ^ 52) ((b.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) (by omega) := by
  have he : (unpackExponent (spec := Format.binary64) b).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 := by
    simp [unpackExponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hm : (unpackMantissa (spec := Format.binary64) b).toNat = b.toNat % 2 ^ 52 := by
    simp [unpackMantissa, BitVec.extractLsb'_toNat]
  have hsg : unpackSign (spec := Format.binary64) b = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    simp [unpackSign, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    omega
  have e0 : ¬ unpackExponent (spec := Format.binary64) b = -1#11 := by
    intro h; have := congrArg BitVec.toNat h; rw [he] at this; simp at this; omega
  have e1 : ¬ unpackExponent (spec := Format.binary64) b = 0#11 := by
    intro h; have := congrArg BitVec.toNat h; rw [he] at this; simp at this; omega
  unfold UnpackedFloat.unpack
  dsimp only
  rw [ite_eq_right e0, ite_eq_right e1]
  simp only [UnpackedFloat.finite.injEq]
  refine ⟨by simp [hsg, Sign.ofBitVec], ?_, ?_⟩
  · rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt (BitVec.isLt _), hm]
    simp
  · rw [he]
    simp [Format.exponentBias]

theorem unpack_pack_normal (M : Nat) (E : Int) (h : 0 < M) (hm1 : 2 ^ 52 ≤ M) (hm2 : M < 2 ^ 53) (he1 : -1074 ≤ E)
    (he2 : E ≤ 971) :
    UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64 (.finite .positive M E h)) =
      .finite .positive M E h := by
  have hp := pack_normal M E h hm1 hm2 he1 he2
  rw [unpack_normal _ (by rw [hp]; omega) (by rw [hp]; omega) (by rw [hp]; omega)]
  simp only [UnpackedFloat.finite.injEq, true_and]
  rw [hp]
  omega

theorem glue_of_value {N D m : Nat} {ex e q : Int}
    (hv : N * (powSplit 2 ex).1 * (powSplit 10 q).2 = m * (powSplit 10 q).1 * D * (powSplit 2 ex).2) :
    m * (scale e q).2 * (D * (powSplit 2 (ex - (e - 2))).2) = N * (powSplit 2 (ex - (e - 2))).1 * (scale e q).1 := by
  have hadd := powSplit_add 2 (ex - (e - 2)) (e - 2)
  rw [show ex - (e - 2) + (e - 2) = ex by omega] at hadd
  have hp := (powSplit_pos 2 (by decide) ex).2
  rw [scale_eq]
  generalize powSplit 2 ex = p at hadd hv hp
  generalize powSplit 2 (ex - (e - 2)) = w at hadd ⊢
  generalize powSplit 2 (e - 2) = a at hadd ⊢
  generalize powSplit 10 q = t at hv ⊢
  obtain ⟨p1, p2⟩ := p
  obtain ⟨w1, w2⟩ := w
  obtain ⟨a1, a2⟩ := a
  obtain ⟨t1, t2⟩ := t
  simp only at hadd hv hp ⊢
  apply Nat.eq_of_mul_eq_mul_right hp
  calc m * (a2 * t1) * (D * w2) * p2 = m * t1 * D * p2 * (w2 * a2) := by ac_rfl
    _ = N * p1 * t2 * (w2 * a2) := by rw [hv]
    _ = N * t2 * (p1 * (w2 * a2)) := by ac_rfl
    _ = N * t2 * (w1 * a1 * p2) := by rw [hadd]
    _ = N * w1 * (a1 * t2) * p2 := by ac_rfl

theorem fits_mul_one (low high a b : Nat) (incl : Bool) (m : Nat) :
    fits low high a b incl m = fits low high a 1 incl (m * b) := by
  simp [fits]

theorem powSplit_neg_nat (a L : Nat) : powSplit a (-(L : Int)) = (1, a ^ L) := by
  unfold powSplit
  by_cases h : L = 0
  · subst h; simp
  · simp only [show ¬ (0 ≤ -(L : Int)) by omega, ite_false, Int.neg_neg, Int.toNat_natCast]

theorem decompose_facts {x : Float} (hx : finiteFloat x = true) {s : Bool} {M : Nat} {e : Int}
    (hd : decompose x = (s, M, e)) (hM : M ≠ 0) :
    M < 2 ^ 53 ∧ -1074 ≤ e ∧ e ≤ 971 ∧ (M < 2 ^ 52 → e = -1074) := by
  have hlt := x.toBits.toNat_lt
  unfold finiteFloat at hx
  simp only [bne_iff_ne, ne_eq] at hx
  unfold decompose at hd
  simp only at hd
  split at hd
  · simp only [Prod.mk.injEq] at hd
    obtain ⟨-, rfl, rfl⟩ := hd
    omega
  · simp only [Prod.mk.injEq] at hd
    obtain ⟨-, rfl, rfl⟩ := hd
    omega

theorem toDigits_length_le_log2 (m : Nat) : (Nat.toDigits 10 m).length ≤ m.log2 + 1 := by
  apply (Nat.length_toDigits_le_iff (by decide) (by omega)).mpr
  calc m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
    _ ≤ 10 ^ (m.log2 + 1) := Nat.pow_le_pow_left (by decide) _

theorem powSplit_of_nonneg (a : Nat) {q : Int} (hq : 0 ≤ q) : powSplit a q = (a ^ q.toNat, 1) := by
  simp [powSplit, hq]

theorem powSplit_of_neg (a : Nat) {q : Int} (hq : q < 0) : powSplit a q = (1, a ^ (-q).toNat) := by
  simp [powSplit, show ¬ 0 ≤ q by omega]

theorem scale_fst_pos (e q : Int) : 0 < (scale e q).1 := by
  rw [scale_eq]
  exact Nat.mul_pos (powSplit_pos 2 (by decide) _).1 (powSplit_pos 10 (by decide) _).2

theorem model_ofScientific {x : Float} (hx : finiteFloat x = true) {M : Nat} {e : Int}
    (hd : decompose x = (false, M, e)) (hM : M ≠ 0) {m : Nat} {q : Int} (hr : roundsTo M e m q = true) :
    UnpackedFloat.ofScientific Format.binary64 m q = .finite .positive M e (Nat.pos_of_ne_zero hM) := by
  obtain ⟨hM53, he1, -, hsub⟩ := decompose_facts hx hd hM
  obtain ⟨-, hr'⟩ := decompose_spec x hx false M e hd
  obtain ⟨hl1, hl2⟩ := hr' hM
  unfold roundsTo at hr
  simp only at hr
  obtain ⟨hm0, hb1, hb2⟩ := interval_bounds M e hM hl1 hl2 _ _ m q hr
  have hn := toDigits_length_le_log2 m
  rw [fits_mul_one] at hr
  have hQ := scale_fst_pos e q
  have h2048 : (2 : Int) ^ Format.binary64.exponentBits = 2048 := rfl
  unfold UnpackedFloat.ofScientific
  rw [dite_eq_right hm0, h2048, ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases hq : 0 ≤ q
  · rw [ite_eq_left hq]
    unfold UnpackedFloat.mul
    have hmb : Format.binary64.mantissaBits = 53 := rfl
    simp only [hmb]
    have hsg : Sign.positive * Sign.positive = Sign.positive := rfl
    rw [hsg]
    have hN : (m <<< 53) * 10 ^ q.toNat = m * 2 ^ 53 * 10 ^ q.toNat := by rw [Nat.shiftLeft_eq]
    apply roundWithAccuracy_eq .positive hM hM53 he1 hsub (Nat.one_pos) (represents_exact _) _ hQ _ hr
    · left
      apply (Nat.le_log2 (by rw [hN]; exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hm0)
        (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))))).mpr
      rw [hN]
      calc 2 ^ 52 ≤ 1 * 2 ^ 53 * 1 := by decide
        _ ≤ m * 2 ^ 53 * 10 ^ q.toNat :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hm0)) (Nat.pow_pos (by decide))
    · apply glue_of_value
      rw [show (-((53 : Nat) : Int) + 0) = -((53 : Nat) : Int) by omega, powSplit_neg_nat,
        powSplit_of_nonneg 10 hq, hN]
      simp only [Nat.mul_one]
      ac_rfl
  · rw [ite_eq_right hq]
    unfold UnpackedFloat.div
    dsimp only
    obtain ⟨sh, hdc, hprec⟩ := divCore_spec m (10 ^ (-q).toNat) 0 0 (Nat.pos_of_ne_zero hm0) (Nat.pow_pos (by decide))
    rw [hdc]
    have hsg : Sign.positive / Sign.positive = Sign.positive := rfl
    simp only [hsg]
    apply roundWithAccuracy_eq .positive hM hM53 he1 hsub (Nat.pow_pos (by decide))
      (represents_ofMantissaAndAccuracy _ _ (Nat.pow_pos (by decide))) hprec hQ _ hr
    apply glue_of_value
    rw [show (0 : Int) - 0 - (sh : Int) = -((sh : Nat) : Int) by omega, powSplit_neg_nat,
      powSplit_of_neg 10 (by omega : q < 0)]
    simp only [Nat.mul_one]
    ac_rfl

theorem ofNat_eq (m : Nat) (hm : 0 < m) (hm53 : m < 2 ^ 53) :
    UnpackedFloat.ofNat Format.binary64 m =
      .finite .positive (m * 2 ^ (52 - m.log2)) ((m.log2 : Int) - 52)
        (Nat.mul_pos hm (Nat.pow_pos (by decide))) := by
  have hL : m.log2 < 53 := (Nat.log2_lt (by omega)).mpr hm53
  have hL1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le (by omega)
  have hL2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  have hM1 : 2 ^ 52 ≤ m * 2 ^ (52 - m.log2) := by
    calc 2 ^ 52 = 2 ^ m.log2 * 2 ^ (52 - m.log2) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ m * 2 ^ (52 - m.log2) := Nat.mul_le_mul_right _ hL1
  have hM2 : m * 2 ^ (52 - m.log2) < 2 ^ 53 := by
    calc m * 2 ^ (52 - m.log2) < 2 ^ (m.log2 + 1) * 2 ^ (52 - m.log2) :=
          Nat.mul_lt_mul_of_pos_right hL2 (Nat.pow_pos (by decide))
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  have hlogM : (m * 2 ^ (52 - m.log2)).log2 = 52 := by
    have h1 := (Nat.le_log2 (n := m * 2 ^ (52 - m.log2)) (by omega)).mpr hM1
    have h2 := (Nat.log2_lt (n := m * 2 ^ (52 - m.log2)) (by omega)).mpr hM2
    omega
  unfold UnpackedFloat.ofNat UnpackedFloat.ofInt UnpackedFloat.normalize
  have hc : compare (m : Int) 0 = .gt := by
    rw [Int.compare_eq_gt]; omega
  rw [hc]
  dsimp only
  unfold UnpackedFloat.round decreaseExponent
  simp only [targetExponent_binary64, totalExponent, Int.toNat_natCast, Nat.shiftLeft_eq]
  have hT : max ((m.log2 : Int) + 1 + 0 - 53) (-1074) = (m.log2 : Int) - 52 := by omega
  have hs : (0 - ((m.log2 : Int) - 52)).toNat = 52 - m.log2 := by omega
  simp only [hT, hs]
  have he : (0 : Int) - ((52 - m.log2 : Nat) : Int) = (m.log2 : Int) - 52 := by omega
  rw [he]
  apply roundWithAccuracy_eq .positive (Nat.ne_of_gt (by omega)) hM2 (by omega) (fun h => by omega)
    Nat.one_pos (by simpa using represents_exact (m * 2 ^ (52 - m.log2))) (Or.inl (by omega)) Nat.one_pos
    (Pw := 4 * (m * 2 ^ (52 - m.log2)))
  · rw [show (m.log2 : Int) - 52 - ((m.log2 : Int) - 52 - 2) = ((2 : Nat) : Int) by omega, powSplit_nat]
    simp only [Nat.mul_one]
    rw [Nat.mul_comm]
  · rw [fits_iff]
    simp only [roundingInterval]
    constructor
    · left
      split <;> omega
    · left
      omega

theorem toFloat_unpack (m : Nat) (hm : 0 < m) (hm53 : m < 2 ^ 53) :
    m.toUInt64.toFloat.toModel.unpack =
      .finite .positive (m * 2 ^ (52 - m.log2)) ((m.log2 : Int) - 52)
        (Nat.mul_pos hm (Nat.pow_pos (by decide))) := by
  have hm64 : m.toUInt64.toNat = m := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
  have : m.toUInt64.toFloat.toModel.unpack =
      UnpackedFloat.unpack Format.binary64 (UnpackedFloat.pack Format.binary64
        (UnpackedFloat.ofNat Format.binary64 m.toUInt64.toNat)) := rfl
  rw [this, hm64, ofNat_eq m hm hm53]
  have hL : m.log2 < 53 := (Nat.log2_lt (by omega)).mpr hm53
  have hL1 : 2 ^ m.log2 ≤ m := Nat.log2_self_le (by omega)
  have hL2 : m < 2 ^ (m.log2 + 1) := Nat.lt_log2_self
  apply unpack_pack_normal
  · calc 2 ^ 52 = 2 ^ m.log2 * 2 ^ (52 - m.log2) := by rw [← Nat.pow_add]; congr 1; omega
      _ ≤ m * 2 ^ (52 - m.log2) := Nat.mul_le_mul_right _ hL1
  · calc m * 2 ^ (52 - m.log2) < 2 ^ (m.log2 + 1) * 2 ^ (52 - m.log2) :=
          Nat.mul_lt_mul_of_pos_right hL2 (Nat.pow_pos (by decide))
      _ = 2 ^ 53 := by rw [← Nat.pow_add]; congr 1; omega
  · omega
  · omega

theorem ofBits_unpack (c : UInt64) (h1 : c.toNat / 2 ^ 52 % 2 ^ 11 ≠ 0) (h2 : c.toNat / 2 ^ 52 % 2 ^ 11 ≠ 2047)
    (h3 : c.toNat < 2 ^ 63) :
    (Float.ofBits c).toModel.unpack =
      .finite .positive (2 ^ 52 + c.toNat % 2 ^ 52) ((c.toNat / 2 ^ 52 % 2 ^ 11 : Nat) - 1075) (by omega) := by
  have : (Float.ofBits c).toModel.unpack = UnpackedFloat.unpack Format.binary64
      (UnpackedFloat.pack Format.binary64 (UnpackedFloat.unpack Format.binary64 c.toBitVec)) := rfl
  rw [this, unpack_normal c.toBitVec (by simpa using h1) (by simpa using h2) (by simpa using h3)]
  simp only [UInt64.toNat_toBitVec]
  exact unpack_pack_normal _ _ _ (by omega) (by omega) (by omega) (by omega)

theorem table_unpack (k : Nat) (hk : k ≤ 22) (h : k < Float.exactlyRepresentablePowersOfTen.size) :
    ∃ P F hP, (Float.exactlyRepresentablePowersOfTen[k]'h).toModel.unpack = .finite .positive P F hP ∧
      P * (powSplit 2 F).1 = 10 ^ k * (powSplit 2 F).2 := by
  rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨
      k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 16 ∨ k = 17 ∨ k = 18 ∨ k = 19 ∨
      k = 20 ∨ k = 21 ∨ k = 22) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_, _, _, ofBits_unpack _ (by decide) (by decide) (by decide), by decide⟩

theorem div_value {M₁ M₂ v₁ v₂ : Nat} {E₁ E₂ : Int} (sh : Nat)
    (h₁ : M₁ * (powSplit 2 E₁).1 = v₁ * (powSplit 2 E₁).2) (h₂ : M₂ * (powSplit 2 E₂).1 = v₂ * (powSplit 2 E₂).2) :
    M₁ * 2 ^ sh * (powSplit 2 (E₁ - E₂ - sh)).1 * v₂ = v₁ * M₂ * (powSplit 2 (E₁ - E₂ - sh)).2 := by
  have hA := powSplit_add 2 (E₁ - E₂ - sh) (E₂ + sh)
  rw [show E₁ - E₂ - sh + (E₂ + sh) = E₁ by omega] at hA
  have hB := powSplit_add 2 E₂ sh
  rw [powSplit_nat] at hB
  simp only [Nat.mul_one] at hB
  have pe := (powSplit_pos 2 (by decide) E₁).2
  have pf := (powSplit_pos 2 (by decide) E₂).2
  have pg := (powSplit_pos 2 (by decide) (E₂ + sh)).2
  generalize powSplit 2 (E₁ - E₂ - sh) = x at hA ⊢
  generalize powSplit 2 (E₂ + sh) = g at hA hB pg
  generalize powSplit 2 E₁ = a at hA h₁ pe
  generalize powSplit 2 E₂ = f at hB h₂ pf
  obtain ⟨x1, x2⟩ := x
  obtain ⟨g1, g2⟩ := g
  obtain ⟨a1, a2⟩ := a
  obtain ⟨f1, f2⟩ := f
  simp only at hA hB h₁ h₂ pe pf pg ⊢
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.mul_pos pe pf) pg)
  calc M₁ * 2 ^ sh * x1 * v₂ * (a2 * f2 * g2) = M₁ * x1 * a2 * (v₂ * f2) * (2 ^ sh * g2) := by ac_rfl
    _ = M₁ * x1 * a2 * (M₂ * f1) * (2 ^ sh * g2) := by rw [← h₂]
    _ = M₁ * M₂ * x1 * a2 * (f1 * 2 ^ sh * g2) := by ac_rfl
    _ = M₁ * M₂ * x1 * a2 * (g1 * f2) := by rw [hB]
    _ = M₁ * M₂ * f2 * (x1 * g1 * a2) := by ac_rfl
    _ = M₁ * M₂ * f2 * (a1 * (x2 * g2)) := by rw [hA]
    _ = (M₁ * a1) * M₂ * x2 * f2 * g2 := by ac_rfl
    _ = (v₁ * a2) * M₂ * x2 * f2 * g2 := by rw [h₁]
    _ = v₁ * M₂ * x2 * (a2 * f2 * g2) := by ac_rfl

theorem mul_value {M₁ M₂ v₁ v₂ : Nat} {E₁ E₂ : Int}
    (h₁ : M₁ * (powSplit 2 E₁).1 = v₁ * (powSplit 2 E₁).2) (h₂ : M₂ * (powSplit 2 E₂).1 = v₂ * (powSplit 2 E₂).2) :
    M₁ * M₂ * (powSplit 2 (E₁ + E₂)).1 = v₁ * v₂ * (powSplit 2 (E₁ + E₂)).2 := by
  have hA := powSplit_add 2 E₁ E₂
  have pe := (powSplit_pos 2 (by decide) E₁).2
  have pf := (powSplit_pos 2 (by decide) E₂).2
  generalize powSplit 2 (E₁ + E₂) = x at hA ⊢
  generalize powSplit 2 E₁ = a at hA h₁ pe
  generalize powSplit 2 E₂ = f at hA h₂ pf
  obtain ⟨x1, x2⟩ := x
  obtain ⟨a1, a2⟩ := a
  obtain ⟨f1, f2⟩ := f
  simp only at hA h₁ h₂ pe pf ⊢
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos pe pf)
  calc M₁ * M₂ * x1 * (a2 * f2) = M₁ * M₂ * (x1 * (a2 * f2)) := by ac_rfl
    _ = M₁ * M₂ * (a1 * f1 * x2) := by rw [hA]
    _ = (M₁ * a1) * (M₂ * f1) * x2 := by ac_rfl
    _ = (v₁ * a2) * (v₂ * f2) * x2 := by rw [h₁, h₂]
    _ = v₁ * v₂ * x2 * (a2 * f2) := by ac_rfl

theorem toFloat_value (m : Nat) (hm53 : m < 2 ^ 53) :
    m * 2 ^ (52 - m.log2) * (powSplit 2 ((m.log2 : Int) - 52)).1 = m * (powSplit 2 ((m.log2 : Int) - 52)).2 := by
  have hL : m.log2 ≤ 52 := by
    by_cases h : m = 0
    · subst h; decide
    · have := (Nat.log2_lt h).mpr hm53; omega
  rw [show (m.log2 : Int) - 52 = -((52 - m.log2 : Nat) : Int) by omega, powSplit_neg_nat]
  simp

theorem div_toBits (a b : Float) : (a / b).toBits = UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.div Format.binary64 a.toModel.unpack b.toModel.unpack)) := rfl

theorem mul_toBits (a b : Float) : (a * b).toBits = UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
    (UnpackedFloat.mul Format.binary64 a.toModel.unpack b.toModel.unpack)) := rfl

theorem ofModel_ofScientific_toBits (m : Nat) (q : Int) : (Float.ofModel (Float.Model.ofScientific m q)).toBits =
    UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (UnpackedFloat.ofScientific Format.binary64 m q)) := rfl

end ExactJSON.FloatText

namespace ExactJSON

open FloatText Float.Model Float.Model.UnpackedFloat

theorem ofScientificRounds : OfScientificRounds := by
  intro x M e m q hx hd hM hr
  apply toBits_inj
  obtain ⟨hM53, he1, -, hsub⟩ := decompose_facts hx hd hM
  obtain ⟨-, hr'⟩ := decompose_spec x hx false M e hd
  obtain ⟨hl1, hl2⟩ := hr' hM
  have hr0 := hr
  unfold roundsTo at hr
  simp only at hr
  obtain ⟨hm0, hb1, hb2⟩ := interval_bounds M e hM hl1 hl2 _ _ m q hr
  rw [fits_mul_one] at hr
  have hQ := scale_fst_pos e q
  have hpack := pack_decompose hx hd (Nat.pos_of_ne_zero hM)
  have hxb : UInt64.ofBitVec x.toBits.toBitVec = x.toBits := rfl
  unfold Float.ofScientific
  split
  · rename_i hfast
    obtain ⟨hm53, hk⟩ := hfast
    have hmu := toFloat_unpack m (Nat.pos_of_ne_zero hm0) hm53
    have hL : m.log2 ≤ 52 := by have := (Nat.log2_lt hm0).mpr hm53; omega
    have hMm : 2 ^ 52 ≤ m * 2 ^ (52 - m.log2) := by
      calc 2 ^ 52 = 2 ^ m.log2 * 2 ^ (52 - m.log2) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ m * 2 ^ (52 - m.log2) := Nat.mul_le_mul_right _ (Nat.log2_self_le hm0)
    obtain ⟨P, F, hP, hu, hPv⟩ := table_unpack q.natAbs hk (by
      rw [show Float.exactlyRepresentablePowersOfTen.size = 23 by decide]; omega)
    dsimp only
    split
    · rename_i hs
      have hq : q < 0 := by simpa using hs
      rw [div_toBits, hmu, hu]
      unfold UnpackedFloat.div
      dsimp only
      obtain ⟨sh, hdc, hprec⟩ := divCore_spec (m * 2 ^ (52 - m.log2)) P ((m.log2 : Int) - 52) F
        (Nat.mul_pos (Nat.pos_of_ne_zero hm0) (Nat.pow_pos (by decide))) hP
      rw [hdc]
      dsimp only
      rw [show Sign.positive / Sign.positive = Sign.positive from rfl,
        roundWithAccuracy_eq .positive hM hM53 he1 hsub hP (represents_ofMantissaAndAccuracy _ _ hP) hprec hQ _ hr,
        hpack, hxb]
      apply glue_of_value
      rw [powSplit_of_neg 10 hq, show (-q).toNat = q.natAbs by omega]
      have := div_value sh (toFloat_value m hm53) hPv
      simp only [Nat.mul_one] at this ⊢
      rw [this]
    · rename_i hs
      have hq : 0 ≤ q := by simp only [decide_eq_true_eq, Int.not_lt] at hs; exact hs
      rw [mul_toBits, hmu, hu]
      unfold UnpackedFloat.mul
      dsimp only
      rw [show Sign.positive * Sign.positive = Sign.positive from rfl,
        roundWithAccuracy_eq .positive hM hM53 he1 hsub Nat.one_pos (represents_exact _) _ hQ _ hr,
        hpack, hxb]
      · left
        have hpos : 0 < m * 2 ^ (52 - m.log2) := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hMm
        apply (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos hpos hP))).mpr
        exact Nat.le_trans hMm (Nat.le_mul_of_pos_right _ hP)
      · apply glue_of_value
        rw [powSplit_of_nonneg 10 hq, show q.toNat = q.natAbs by omega]
        have := mul_value (toFloat_value m hm53) hPv
        simp only [Nat.mul_one] at this ⊢
        rw [this]
  · rename_i hslow
    dsimp only
    rw [ofModel_ofScientific_toBits]
    have hq : (if decide (q < 0) = true then Int.negOfNat q.natAbs else Int.ofNat q.natAbs) = q := by
      split
      · rename_i h
        simp only [decide_eq_true_eq] at h
        rw [Int.negOfNat_eq, Int.ofNat_eq_natCast]
        omega
      · rename_i h
        simp only [decide_eq_true_eq] at h
        rw [Int.ofNat_eq_natCast]
        omega
    rw [hq, model_ofScientific hx hd hM hr0, hpack, hxb]

end ExactJSON
