module

public import ExactJSON.OfScientific

public section

namespace ExactJSON.FloatText

open Float.Model Float.Model.UnpackedFloat

theorem fits_transport {low high : Nat} {incl : Bool} {P Q K D : Nat} (hQ : 0 < Q) (hD : 0 < D)
    (h : P * D = K * Q) : fits low high Q 1 incl P = fits low high D 1 incl K := by
  have tl := transport hQ hD h low
  have th := transport hQ hD h high
  have e1 : P = high * Q ↔ K = high * D := by
    rw [eq_comm, th.2.2.1, eq_comm]
  rw [Bool.eq_iff_iff, fits_iff, fits_iff, tl.1, tl.2.2.1, th.2.1, e1]

theorem rounded_bounds {N D' r : Nat} (hD' : 0 < D')
    (hreq : r = if 2 * (N % D') < D' then N / D' else if 2 * (N % D') = D' then N / D' + N / D' % 2 else N / D' + 1) :
    (2 * (r * D') < 2 * N + D' ∨ (2 * (r * D') = 2 * N + D' ∧ r % 2 = 0)) ∧
      (2 * N < 2 * (r * D') + D' ∨ (2 * N = 2 * (r * D') + D' ∧ r % 2 = 0)) ∧
      N / D' ≤ r ∧ r ≤ N / D' + 1 := by
  have hN := Nat.div_add_mod N D'
  have hR := Nat.mod_lt N hD'
  generalize N / D' = a at hN hreq ⊢
  generalize N % D' = R at hN hR hreq
  subst hN
  rw [Nat.mul_comm D' a]
  by_cases c1 : 2 * R < D'
  · rw [ite_eq_left c1] at hreq
    subst hreq
    exact ⟨Or.inl (by omega), Or.inl (by omega), by omega, by omega⟩
  · rw [ite_eq_right c1] at hreq
    by_cases c2 : 2 * R = D'
    · rw [ite_eq_left c2] at hreq
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · rw [ha, Nat.add_zero] at hreq
        subst hreq
        exact ⟨Or.inl (by omega), Or.inr ⟨by omega, ha⟩, by omega, by omega⟩
      · rw [ha] at hreq
        subst hreq
        have : (a + 1) * D' = a * D' + D' := Nat.succ_mul a D'
        rw [this]
        exact ⟨Or.inr ⟨by omega, by omega⟩, Or.inl (by omega), by omega, by omega⟩
    · rw [ite_eq_right c2] at hreq
      subst hreq
      have : (a + 1) * D' = a * D' + D' := Nat.succ_mul a D'
      rw [this]
      exact ⟨Or.inl (by omega), Or.inl (by omega), by omega, by omega⟩

theorem fits_rounded {N D' r : Nat} (hD' : 0 < D') (hr0 : 1 ≤ r) (lc : Bool) (hlc : lc = true → r * D' ≤ N)
    (hA : 2 * (r * D') < 2 * N + D' ∨ (2 * (r * D') = 2 * N + D' ∧ r % 2 = 0))
    (hB : 2 * N < 2 * (r * D') + D' ∨ (2 * N = 2 * (r * D') + D' ∧ r % 2 = 0)) :
    fits (roundingInterval r lc).1 (roundingInterval r lc).2.2 D' 1 (r % 2 == 0) (4 * N) = true := by
  rw [fits_iff]
  have h4 : (4 * r - 2) * D' = 4 * (r * D') - 2 * D' := by rw [Nat.sub_mul, Nat.mul_assoc]
  have h1 : (4 * r - 1) * D' = 4 * (r * D') - 1 * D' := by rw [Nat.sub_mul, Nat.mul_assoc]
  have h2 : (4 * r + 2) * D' = 4 * (r * D') + 2 * D' := by rw [Nat.add_mul, Nat.mul_assoc]
  have hrD : 1 * D' ≤ r * D' := Nat.mul_le_mul_right _ hr0
  have hup : 4 * N < (4 * r + 2) * D' ∨ ((r % 2 == 0) = true ∧ 4 * N = (4 * r + 2) * D') := by
    rcases hB with hB | ⟨hB, hev⟩
    · left; omega
    · right; exact ⟨by simp [hev], by omega⟩
  unfold roundingInterval
  cases lc with
  | true =>
    have hn := hlc rfl
    simp only [ite_true]
    exact ⟨Or.inl (by omega), hup⟩
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    refine ⟨?_, hup⟩
    rcases hA with hA | ⟨hA, hev⟩
    · left; omega
    · right; exact ⟨by simp [hev], by omega⟩

theorem fits_rounded_up {N D' : Nat} (hA : 2 * (2 ^ 53 * D') ≤ 2 * N + D') (hN : N < 2 ^ 53 * D') :
    fits (roundingInterval (2 ^ 52) true).1 (roundingInterval (2 ^ 52) true).2.2 D' 1 (2 ^ 52 % 2 == 0) (2 * N) =
      true := by
  rw [fits_iff]
  unfold roundingInterval
  simp only [ite_true]
  have h1 : (4 * 2 ^ 52 - 1) * D' = 2 * (2 ^ 53 * D') - D' := by
    rw [Nat.sub_mul, ← Nat.mul_assoc, Nat.one_mul]
  have h2 : (4 * 2 ^ 52 + 2) * D' = 2 * (2 ^ 53 * D') + 2 * D' := by
    rw [Nat.add_mul, ← Nat.mul_assoc]
  have hev : ((2 : Nat) ^ 52 % 2 == 0) = true := by decide
  rw [h1, h2, hev]
  generalize 2 ^ 53 * D' = X at hA hN ⊢
  constructor
  · by_cases heq : 2 * X - D' = 2 * N
    · exact Or.inr ⟨rfl, heq⟩
    · exact Or.inl (by omega)
  · exact Or.inl (by omega)

theorem roundWithAccuracy_sound (sg : Sign) {mant : Nat} {ex : Int} {acc : Accuracy} {N D : Nat} (hD : 0 < D)
    (hrep : Represents (ExtendedMantissa.ofMantissaAndAccuracy mant acc) N D) (hmant : mant = N / D)
    (hprec : 52 ≤ mant.log2 ∨ ex ≤ -1074) :
    roundWithAccuracy Format.binary64 sg mant ex acc = .zero sg ∨
      ∃ (M' : Nat) (e' : Int) (h : 0 < M'), roundWithAccuracy Format.binary64 sg mant ex acc = .finite sg M' e' h ∧
        M' < 2 ^ 53 ∧ -1074 ≤ e' ∧ (M' < 2 ^ 52 → e' = -1074) ∧
        fits (roundingInterval M' (decide (M' = 2 ^ 52) && decide (e' > -1074))).1
          (roundingInterval M' (decide (M' = 2 ^ 52) && decide (e' > -1074))).2.2
          (D * (powSplit 2 (ex - (e' - 2))).2) 1 (M' % 2 == 0) (N * (powSplit 2 (ex - (e' - 2))).1) = true := by
  obtain ⟨L, hL⟩ : ∃ L, mant.log2 = L := ⟨_, rfl⟩
  rw [hL] at hprec
  obtain ⟨T, hT⟩ : ∃ T, max ((L : Int) + 1 + ex - 53) (-1074) = T := ⟨_, rfl⟩
  have hTex : ex ≤ T := by omega
  have hT0 : -1074 ≤ T := by omega
  have hTL : (L : Int) + 1 + ex - 53 ≤ T := by omega
  have hTn : T > -1074 → T = (L : Int) + 1 + ex - 53 := by omega
  obtain ⟨s, hs⟩ : ∃ s, (T - ex).toNat = s := ⟨_, rfl⟩
  have hs' : (s : Int) = T - ex := by omega
  have hle : L + 1 ≤ 53 + s := by omega
  have hnormL : T > -1074 → 52 ≤ L ∧ 52 + s = L := by
    intro hT1
    have := hTn hT1
    omega
  have hD' : 0 < D * 2 ^ s := Nat.mul_pos hD (Nat.pow_pos (by decide))
  have hdiv53 : N / (D * 2 ^ s) < 2 ^ 53 := by
    apply (Nat.div_lt_iff_lt_mul hD').mpr
    have h2 : mant < 2 ^ (L + 1) := hL ▸ Nat.lt_log2_self
    rw [hmant] at h2
    have h0 := Nat.div_add_mod N D
    have h0' := Nat.mod_lt N hD
    calc N < D * (N / D + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
      _ ≤ D * 2 ^ (L + 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ D * 2 ^ (53 + s) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hle)
      _ = 2 ^ 53 * (D * 2 ^ s) := by rw [Nat.pow_add]; ac_rfl
  have hdiv52 : T > -1074 → 2 ^ 52 ≤ N / (D * 2 ^ s) := by
    intro hT1
    obtain ⟨hL52, hsL⟩ := hnormL hT1
    apply (Nat.le_div_iff_mul_le hD').mpr
    have hm0 : mant ≠ 0 := by
      intro h
      rw [h] at hL
      simp at hL
      omega
    have h2 : 2 ^ L ≤ mant := hL ▸ Nat.log2_self_le hm0
    rw [hmant] at h2
    calc 2 ^ 52 * (D * 2 ^ s) = 2 ^ (52 + s) * D := by rw [Nat.pow_add]; ac_rfl
      _ = 2 ^ L * D := by rw [hsL]
      _ ≤ N / D * D := Nat.mul_le_mul_right _ h2
      _ ≤ N := Nat.div_mul_le_self N D
  have hrep1 := represents_shift hD hrep s
  obtain ⟨r, hr⟩ : ∃ r, (ExtendedMantissa.ofMantissaAndAccuracy mant acc >>> s).roundedMantissa = r := ⟨_, rfl⟩
  have hreq := roundedMantissa_eq hD' hrep1
  rw [hr] at hreq
  obtain ⟨hA, hB, hr1, hr2⟩ := rounded_bounds hD' hreq
  have hr53 : r ≤ 2 ^ 53 := by omega
  have hr52 : T > -1074 → 2 ^ 52 ≤ r := by
    intro hT1
    have := hdiv52 hT1
    omega
  obtain ⟨s₂, hs2⟩ : ∃ s₂, (max ((r.log2 : Int) + 1 + (ex + s) - 53) (-1074) - (ex + s)).toNat = s₂ := ⟨_, rfl⟩
  have hexs : ex + (s : Int) = T := by omega
  rw [hexs] at hs2
  have hcase : (s₂ = 0 ∧ r < 2 ^ 53) ∨ (s₂ = 1 ∧ r = 2 ^ 53) := by
    by_cases hr53' : r < 2 ^ 53
    · left
      have hlog : (r.log2 : Int) ≤ 52 := by
        by_cases hr0 : r = 0
        · rw [hr0]; simp
        · have := (Nat.log2_lt hr0).mpr hr53'
          omega
      exact ⟨by omega, hr53'⟩
    · right
      have hr53e : r = 2 ^ 53 := by omega
      have hlog : r.log2 = 53 := by rw [hr53e]; exact Nat.log2_two_pow
      rw [hlog] at hs2
      exact ⟨by omega, hr53e⟩
  have hR : roundWithAccuracy Format.binary64 sg mant ex acc =
      if h : (ExtendedMantissa.ofMantissaAndAccuracy r .exact >>> s₂).mantissa = 0 then .zero sg
      else .finite sg (ExtendedMantissa.ofMantissaAndAccuracy r .exact >>> s₂).mantissa (T + (s₂ : Int))
        (Nat.pos_of_ne_zero h) := by
    unfold roundWithAccuracy shiftToTargetExponent shiftToExponent
    simp only [targetExponent_binary64, totalExponent, hL, hT, hs, hr, hexs, hs2]
  rw [hR]
  rcases hcase with ⟨rfl, hr53'⟩ | ⟨rfl, hr53e⟩
  · have hX : (ExtendedMantissa.ofMantissaAndAccuracy r .exact >>> 0).mantissa = r := rfl
    by_cases h0 : r = 0
    · left
      rw [dite_eq_left (by rw [hX]; exact h0)]
    · right
      refine ⟨r, T, Nat.pos_of_ne_zero h0, finite_of_eq sg hX (by omega) h0, hr53', hT0, fun h => ?_, ?_⟩
      · by_cases hlt : T > -1074
        · exact absurd (hr52 hlt) (by omega)
        · omega
      · rw [show ex - (T - 2) = ((2 : Nat) : Int) - (s : Int) by omega]
        have hw := powSplit_pos 2 (by decide) (((2 : Nat) : Int) - (s : Int))
        have hsh := powSplit_two_shift 2 s
        rw [fits_transport (K := 4 * N) (D := D * 2 ^ s) (Nat.mul_pos hD hw.2) hD' (by
          calc N * (powSplit 2 (((2 : Nat) : Int) - (s : Int))).1 * (D * 2 ^ s)
              = N * D * ((powSplit 2 (((2 : Nat) : Int) - (s : Int))).1 * 2 ^ s) := by ac_rfl
            _ = N * D * (2 ^ 2 * (powSplit 2 (((2 : Nat) : Int) - (s : Int))).2) := by rw [hsh]
            _ = 4 * N * (D * (powSplit 2 (((2 : Nat) : Int) - (s : Int))).2) := by
              rw [show (2 : Nat) ^ 2 = 4 from rfl]; ac_rfl)]
        apply fits_rounded hD' (Nat.pos_of_ne_zero h0) _ _ hA hB
        intro hlc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hlc
        rw [hlc.1]
        exact (Nat.le_div_iff_mul_le hD').mp (hdiv52 hlc.2)
  · have hX : (ExtendedMantissa.ofMantissaAndAccuracy r .exact >>> 1).mantissa = 2 ^ 52 := by
      rw [hr53e]
      show 2 ^ 53 / 2 = 2 ^ 52
      decide
    right
    refine ⟨2 ^ 52, T + 1, by decide, finite_of_eq sg hX (by omega) (by decide), by decide, by omega,
      fun h => absurd h (by decide), ?_⟩
    rw [show ex - (T + 1 - 2) = ((1 : Nat) : Int) - (s : Int) by omega]
    have hw := powSplit_pos 2 (by decide) (((1 : Nat) : Int) - (s : Int))
    have hsh := powSplit_two_shift 1 s
    rw [fits_transport (K := 2 * N) (D := D * 2 ^ s) (Nat.mul_pos hD hw.2) hD' (by
      calc N * (powSplit 2 (((1 : Nat) : Int) - (s : Int))).1 * (D * 2 ^ s)
          = N * D * ((powSplit 2 (((1 : Nat) : Int) - (s : Int))).1 * 2 ^ s) := by ac_rfl
        _ = N * D * (2 ^ 1 * (powSplit 2 (((1 : Nat) : Int) - (s : Int))).2) := by rw [hsh]
        _ = 2 * N * (D * (powSplit 2 (((1 : Nat) : Int) - (s : Int))).2) := by
          rw [Nat.pow_one]; ac_rfl)]
    have hl : (decide ((2 : Nat) ^ 52 = 2 ^ 52) && decide (T + 1 > -1074)) = true := by
      rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      exact ⟨rfl, by omega⟩
    rw [hl]
    have hA' : 2 * (2 ^ 53 * (D * 2 ^ s)) ≤ 2 * N + D * 2 ^ s := by
      rw [← hr53e]
      rcases hA with hA | ⟨hA, -⟩
      · exact Nat.le_of_lt hA
      · exact Nat.le_of_eq hA
    exact fits_rounded_up hA' ((Nat.div_lt_iff_lt_mul hD').mp hdiv53)

theorem model_round (m : Nat) (q : Int) (hm : m ≠ 0) (hq1 : q ≤ 2048) (hq2 : -((2048 : Int) + m.log2) ≤ q) :
    ∃ (mant : Nat) (ex : Int) (acc : Accuracy) (N D : Nat), 0 < D ∧
      Represents (ExtendedMantissa.ofMantissaAndAccuracy mant acc) N D ∧ mant = N / D ∧
      (52 ≤ mant.log2 ∨ ex ≤ -1074) ∧
      N * (powSplit 2 ex).1 * (powSplit 10 q).2 = m * (powSplit 10 q).1 * D * (powSplit 2 ex).2 ∧
      UnpackedFloat.ofScientific Format.binary64 m q = roundWithAccuracy Format.binary64 .positive mant ex acc := by
  have h2048 : (2 : Int) ^ Format.binary64.exponentBits = 2048 := rfl
  unfold UnpackedFloat.ofScientific
  rw [dite_eq_right hm, h2048, ite_eq_right (by omega), ite_eq_right (by omega)]
  by_cases hq : 0 ≤ q
  · rw [ite_eq_left hq]
    unfold UnpackedFloat.mul
    have hmb : Format.binary64.mantissaBits = 53 := rfl
    simp only [hmb]
    rw [show Sign.positive * Sign.positive = Sign.positive from rfl]
    have hN : (m <<< 53) * 10 ^ q.toNat = m * 2 ^ 53 * 10 ^ q.toNat := by rw [Nat.shiftLeft_eq]
    refine ⟨_, _, _, _, 1, Nat.one_pos, represents_exact _, (Nat.div_one _).symm, ?_, ?_, rfl⟩
    · left
      apply (Nat.le_log2 (by rw [hN]; exact Nat.ne_of_gt (Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero hm)
        (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))))).mpr
      rw [hN]
      calc 2 ^ 52 ≤ 1 * 2 ^ 53 * 1 := by decide
        _ ≤ m * 2 ^ 53 * 10 ^ q.toNat :=
          Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.pos_of_ne_zero hm)) (Nat.pow_pos (by decide))
    · rw [show (-((53 : Nat) : Int) + 0) = -((53 : Nat) : Int) by omega, powSplit_neg_nat,
        powSplit_of_nonneg 10 hq, hN]
      simp only [Nat.mul_one]
      ac_rfl
  · rw [ite_eq_right hq]
    unfold UnpackedFloat.div
    dsimp only
    obtain ⟨sh, hdc, hprec⟩ := divCore_spec m (10 ^ (-q).toNat) 0 0 (Nat.pos_of_ne_zero hm) (Nat.pow_pos (by decide))
    rw [hdc]
    rw [show Sign.positive / Sign.positive = Sign.positive from rfl]
    refine ⟨_, _, _, _, _, Nat.pow_pos (by decide), represents_ofMantissaAndAccuracy _ _ (Nat.pow_pos (by decide)),
      rfl, hprec, ?_, rfl⟩
    rw [show (0 : Int) - 0 - (sh : Int) = -((sh : Nat) : Int) by omega, powSplit_neg_nat,
      powSplit_of_neg 10 (by omega : q < 0)]
    simp only [Nat.mul_one]
    ac_rfl

theorem ofScientific_round (m : Nat) (q : Int) (hm : m ≠ 0) (hq1 : q ≤ 2048)
    (hq2 : -((2048 : Int) + m.log2) ≤ q) :
    ∃ (mant : Nat) (ex : Int) (acc : Accuracy) (N D : Nat), 0 < D ∧
      Represents (ExtendedMantissa.ofMantissaAndAccuracy mant acc) N D ∧ mant = N / D ∧
      (52 ≤ mant.log2 ∨ ex ≤ -1074) ∧
      N * (powSplit 2 ex).1 * (powSplit 10 q).2 = m * (powSplit 10 q).1 * D * (powSplit 2 ex).2 ∧
      (Float.ofScientific m (decide (q < 0)) q.natAbs).toBits =
        UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
          (roundWithAccuracy Format.binary64 .positive mant ex acc)) := by
  unfold Float.ofScientific
  split
  · rename_i hfast
    obtain ⟨hm53, hk⟩ := hfast
    have hmu := toFloat_unpack m (Nat.pos_of_ne_zero hm) hm53
    have hMm : 2 ^ 52 ≤ m * 2 ^ (52 - m.log2) := by
      have hL : m.log2 ≤ 52 := by have := (Nat.log2_lt hm).mpr hm53; omega
      calc 2 ^ 52 = 2 ^ m.log2 * 2 ^ (52 - m.log2) := by rw [← Nat.pow_add]; congr 1; omega
        _ ≤ m * 2 ^ (52 - m.log2) := Nat.mul_le_mul_right _ (Nat.log2_self_le hm)
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
        (Nat.mul_pos (Nat.pos_of_ne_zero hm) (Nat.pow_pos (by decide))) hP
      rw [hdc]
      dsimp only
      rw [show Sign.positive / Sign.positive = Sign.positive from rfl]
      refine ⟨_, _, _, _, _, hP, represents_ofMantissaAndAccuracy _ _ hP, rfl, hprec, ?_, rfl⟩
      rw [powSplit_of_neg 10 hq, show (-q).toNat = q.natAbs by omega]
      have := div_value sh (toFloat_value m hm53) hPv
      simp only [Nat.mul_one] at this ⊢
      rw [this]
    · rename_i hs
      have hq : 0 ≤ q := by simp only [decide_eq_true_eq, Int.not_lt] at hs; exact hs
      rw [mul_toBits, hmu, hu]
      unfold UnpackedFloat.mul
      dsimp only
      rw [show Sign.positive * Sign.positive = Sign.positive from rfl]
      refine ⟨_, _, _, _, 1, Nat.one_pos, represents_exact _, (Nat.div_one _).symm, ?_, ?_, rfl⟩
      · left
        have hpos : 0 < m * 2 ^ (52 - m.log2) := Nat.lt_of_lt_of_le (Nat.pow_pos (by decide)) hMm
        apply (Nat.le_log2 (Nat.ne_of_gt (Nat.mul_pos hpos hP))).mpr
        exact Nat.le_trans hMm (Nat.le_mul_of_pos_right _ hP)
      · rw [powSplit_of_nonneg 10 hq, show q.toNat = q.natAbs by omega]
        have := mul_value (toFloat_value m hm53) hPv
        simp only [Nat.mul_one] at this ⊢
        rw [this]
  · dsimp only
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
    rw [hq]
    obtain ⟨mant, ex, acc, N, D, hD, hrep, hmant, hprec, hv, heq⟩ := model_round m q hm hq1 hq2
    exact ⟨mant, ex, acc, N, D, hD, hrep, hmant, hprec, hv, by rw [heq]⟩

theorem bits_split {b B F : Nat} (h : b = B * 2 ^ 52 + F) (hF : F < 2 ^ 52) (hB : B ≤ 2046) :
    b / 2 ^ 52 % 2 ^ 11 = B ∧ b % 2 ^ 52 = F ∧ b < 2 ^ 63 := by
  subst h
  have e : B * 2 ^ 52 + F = F + 2 ^ 52 * B := by rw [Nat.add_comm, Nat.mul_comm]
  refine ⟨?_, ?_, by omega⟩
  · rw [e, Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt hF, Nat.zero_add]
    exact Nat.mod_eq_of_lt (by omega)
  · rw [e, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt hF

theorem decompose_of_pack {y : Float} {M' : Nat} {e' : Int} (hM' : 0 < M') (hM53 : M' < 2 ^ 53)
    (he1 : -1074 ≤ e') (he2 : e' ≤ 971) (hsub : M' < 2 ^ 52 → e' = -1074)
    (hy : y.toBits = UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (.finite .positive M' e' hM'))) :
    decompose y = (false, M', e') ∧ finiteFloat y = true := by
  have hb : y.toBits.toNat = (UnpackedFloat.pack Format.binary64 (.finite .positive M' e' hM')).toNat := by
    rw [hy, UInt64.toNat_ofBitVec]
  obtain ⟨B, F, hBF, hF, hB, hc⟩ : ∃ B F : Nat, y.toBits.toNat = B * 2 ^ 52 + F ∧ F < 2 ^ 52 ∧ B ≤ 2046 ∧
      ((B = 0 ∧ F = M' ∧ e' = -1074) ∨ (B ≠ 0 ∧ F + 2 ^ 52 = M' ∧ (B : Int) - 1075 = e')) := by
    by_cases hn : 2 ^ 52 ≤ M'
    · rw [pack_normal M' e' hM' hn hM53 he1 he2] at hb
      refine ⟨(e' + 1075).toNat, M' - 2 ^ 52, hb, ?_, ?_, Or.inr ⟨?_, ?_, ?_⟩⟩ <;> clear hb hy <;> omega
    · have he : e' = -1074 := hsub (by omega)
      subst he
      rw [pack_subnormal M' hM' (by omega)] at hb
      refine ⟨0, M', ?_, ?_, ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩ <;> clear hy <;> omega
  obtain ⟨h1, h2, h3⟩ := bits_split hBF hF hB
  have h3' : ¬ (y.toBits.toNat ≥ 2 ^ 63) := by omega
  constructor
  · unfold decompose
    simp only [h1, h2, h3', decide_false]
    rcases hc with ⟨rfl, rfl, rfl⟩ | ⟨hB0, rfl, rfl⟩
    · rfl
    · rw [ite_eq_right hB0]
  · unfold finiteFloat
    rw [h1]
    simp only [bne_iff_ne, ne_eq]
    omega

theorem pack_overflow {M' : Nat} {e' : Int} (hM' : 0 < M') (he : 972 ≤ e') :
    UnpackedFloat.pack Format.binary64 (.finite .positive M' e' hM') = packedInfinity Format.binary64 .positive := by
  unfold UnpackedFloat.pack
  dsimp only
  split
  · rfl
  · rename_i hc
    simp only [Format.exponentBias] at hc
    omega

theorem zero_bits : UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 (.zero .positive)) = (0.0 : Float).toBits := by
  decide +kernel

theorem inf_bits : UInt64.ofBitVec (packedInfinity Format.binary64 .positive) =
    (Float.ofBits 0x7FF0000000000000).toBits := by
  decide +kernel

theorem inf_not_finite : finiteFloat (Float.ofBits 0x7FF0000000000000) = false := by
  decide +kernel

theorem neg_inf_not_finite : finiteFloat (-(Float.ofBits 0x7FF0000000000000)) = false := by
  decide +kernel

theorem decompose_zero : decompose (0.0 : Float) = (false, 0, -1074) := by
  decide +kernel

theorem decompose_neg_zero : decompose (-0.0 : Float) = (true, 0, -1074) := by
  decide +kernel

theorem floatOf?_cases {neg : Bool} {m : Nat} {q : Int} {x : Float} (h : floatOf? neg m q = some x) :
    x = (if neg then -0.0 else 0.0) ∨
      (m ≠ 0 ∧ -324 ≤ ((Nat.toDigits 10 m).length : Int) + q ∧ ((Nat.toDigits 10 m).length : Int) + q ≤ 309 ∧
        finiteFloat x = true ∧
        x = if neg then -Float.ofScientific m (decide (q < 0)) q.natAbs
          else Float.ofScientific m (decide (q < 0)) q.natAbs) := by
  have hsome : ∀ z : Float, (if finiteFloat z = true then some z else none) = some x → x = z := by
    intro z hz
    split at hz
    · exact (Option.some.inj hz).symm
    · cases hz
  by_cases hm0 : m = 0
  · left
    unfold floatOf? at h
    rw [ite_eq_left hm0] at h
    simp only [Option.map_some] at h
    exact hsome _ h
  · by_cases h2 : ((Nat.toDigits 10 m).length : Int) + q > 309
    · unfold floatOf? at h
      rw [ite_eq_right hm0] at h
      simp only [h2, ite_true, Option.map_none] at h
      cases h
    · by_cases h1 : ((Nat.toDigits 10 m).length : Int) + q < -324
      · left
        unfold floatOf? at h
        rw [ite_eq_right hm0] at h
        simp only [h2, h1, ite_true, ite_false, Option.map_some] at h
        exact hsome _ h
      · right
        rw [floatOf?_eq neg m q hm0 (by omega) (by omega)] at h
        simp only at h
        have hx := hsome _ h
        refine ⟨hm0, by omega, by omega, ?_, hx⟩
        rw [hx] at h ⊢
        cases hf : finiteFloat (if neg = true then -Float.ofScientific m (decide (q < 0)) q.natAbs
          else Float.ofScientific m (decide (q < 0)) q.natAbs)
        · rw [hf] at h
          cases h
        · rfl

end ExactJSON.FloatText

namespace ExactJSON

open FloatText Float.Model Float.Model.UnpackedFloat

theorem floatOf?_sound {x : Float} (hx : finiteFloat x = true) {s : Bool} {M : Nat} {e : Int}
    (hd : FloatText.decompose x = (s, M, e)) (hM : M ≠ 0) {neg : Bool} {m : Nat} {q : Int}
    (h : floatOf? neg m q = some x) : neg = s ∧ FloatText.roundsTo M e m q = true := by
  have hzero : ∀ b : Bool, x ≠ (if b then -0.0 else 0.0) := by
    intro b hb
    rw [hb] at hd
    cases b
    · rw [show (if false = true then -0.0 else (0.0 : Float)) = 0.0 from rfl, decompose_zero] at hd
      simp only [Prod.mk.injEq] at hd
      exact hM hd.2.1.symm
    · rw [show (if true = true then -0.0 else (0.0 : Float)) = -0.0 from rfl, decompose_neg_zero] at hd
      simp only [Prod.mk.injEq] at hd
      exact hM hd.2.1.symm
  rcases floatOf?_cases h with hz | ⟨hm0, h1, h2, -, hxy⟩
  · exact absurd hz (hzero neg)
  have hn := toDigits_length_le_log2 m
  have hn1 : 1 ≤ (Nat.toDigits 10 m).length := List.length_pos_iff.mpr Nat.toDigits_ne_nil
  obtain ⟨mant, ex, acc, N, D, hD, hrep, hmant, hprec, hv, hbits⟩ :=
    ofScientific_round m q hm0 (by omega) (by omega)
  generalize Float.ofScientific m (decide (q < 0)) q.natAbs = y at hxy hbits
  rcases roundWithAccuracy_sound .positive hD hrep hmant hprec with hz | ⟨M', e', hM', hfin', hM53, he1, hsub, hfits⟩
  · rw [hz, zero_bits] at hbits
    have hy0 : y = 0.0 := toBits_inj hbits
    rw [hy0] at hxy
    exact absurd hxy (hzero neg)
  rw [hfin'] at hbits
  by_cases he2 : e' ≤ 971
  · obtain ⟨hdy, hfy⟩ := decompose_of_pack hM' hM53 he1 he2 hsub hbits
    have hdx : decompose x = (neg, M', e') := by
      rw [hxy]
      cases neg
      · exact hdy
      · exact decompose_neg hfy hdy
    rw [hd] at hdx
    simp only [Prod.mk.injEq] at hdx
    obtain ⟨rfl, rfl, rfl⟩ := hdx
    refine ⟨rfl, ?_⟩
    unfold roundsTo
    dsimp only
    rw [fits_mul_one, fits_transport (scale_fst_pos e q)
      (Nat.mul_pos hD (powSplit_pos 2 (by decide) (ex - (e - 2))).2) (glue_of_value hv)]
    exact hfits
  · rw [pack_overflow hM' (by omega), inf_bits] at hbits
    have hyinf : y = Float.ofBits 0x7FF0000000000000 := toBits_inj hbits
    rw [hyinf] at hxy
    rw [hxy] at hx
    cases neg
    · exact absurd hx (by rw [show (if false = true then -Float.ofBits 0x7FF0000000000000
        else Float.ofBits 0x7FF0000000000000) = Float.ofBits 0x7FF0000000000000 from rfl, inf_not_finite]; decide)
    · exact absurd hx (by rw [show (if true = true then -Float.ofBits 0x7FF0000000000000
        else Float.ofBits 0x7FF0000000000000) = -Float.ofBits 0x7FF0000000000000 from rfl, neg_inf_not_finite]; decide)

end ExactJSON
