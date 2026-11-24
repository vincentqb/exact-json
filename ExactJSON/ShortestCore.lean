module

public import ExactJSON.ShortestMin

public section

namespace ExactJSON

namespace FloatText

theorem candidate_seventeen (M : Nat) (e : Int) (hM : M ≠ 0) (hM53 : M < 2 ^ 53) (big : Int)
    (hE : tenPowLe big M e = true) (lc incl : Bool)
    (hlc : (decide (M = 2 ^ 52) && decide (e > -1074)) = lc) :
    (candidate M e lc incl (big - (17 : Nat) + 1)).isSome = true := by
  apply candidate_isSome (Nat.pos_of_ne_zero hM)
  rw [show big - ((17 : Nat) : Int) + 1 = big - 16 by omega]
  have w4 := scale_wide M e big hE 4 (by omega)
  have w2 : lc = true → (scale e (big - 16)).2 < 2 * (scale e (big - 16)).1 := by
    intro h
    have hM2 : M = 2 ^ 52 := by
      rw [h] at hlc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hlc
      exact hlc.1
    exact scale_wide M e big hE 2 (by rw [hM2]; decide)
  generalize scale e (big - 16) = ab at w4 w2 ⊢
  obtain ⟨a, b⟩ := ab
  unfold roundingInterval
  have d1 : 4 * M - (4 * M - 2) = 2 := by omega
  have d2 : 4 * M + 2 - 4 * M = 2 := by omega
  cases lc with
  | false =>
    left
    simp only [Bool.false_eq_true, ite_false, d1, d2] at w4 ⊢
    constructor <;> omega
  | true =>
    right
    have := w2 rfl
    simp only [d2]
    omega

theorem candidate_step {M : Nat} {e : Int} {lc incl : Bool} (hM : 0 < M) (k : Int)
    (h : (candidate M e lc incl k).isSome = true) : (candidate M e lc incl (k - 1)).isSome = true := by
  obtain ⟨c', hc'⟩ := Option.isSome_iff_exists.mp h
  have hb := (candidate_best hM hc').1
  apply candidate_isSome_of_InI hM (y := 10 * c')
  have e1 := ten_zpow_succ (k - 1)
  rw [show k - 1 + 1 = k by omega] at e1
  have h10 : ((10 : Nat) : Rat) = 10 := rfl
  have : ((10 * c' : Nat) : Rat) * 10 ^ (k - 1) = (c' : Rat) * 10 ^ k := by
    rw [Rat.natCast_mul, e1, h10]
    grind
  rw [this]
  exact hb

theorem shortest_strong (x : Float) (hx : finiteFloat x = true) (neg : Bool) (M : Nat) (e : Int)
    (hd : decompose x = (neg, M, e)) (hM : M ≠ 0) :
    ∃ D : Decimal, shortest x = some D ∧ D.negative = neg ∧ roundsTo M e D.digits D.exponent = true ∧
      ∀ m q, roundsTo M e m q = true →
        (Nat.toDigits 10 D.digits).length < (Nat.toDigits 10 m).length ∨
        ((Nat.toDigits 10 D.digits).length = (Nat.toDigits 10 m).length ∧
          (((D.digits : Rat) * 10 ^ D.exponent - (M : Rat) * 2 ^ e).abs <
              ((m : Rat) * 10 ^ q - (M : Rat) * 2 ^ e).abs ∨
            (((D.digits : Rat) * 10 ^ D.exponent - (M : Rat) * 2 ^ e).abs =
                ((m : Rat) * 10 ^ q - (M : Rat) * 2 ^ e).abs ∧
              ((m = D.digits ∧ q = D.exponent) ∨ (D.digits % 2 = 0 ∧ m % 2 = 1))))) := by
  have hM0 : 0 < M := Nat.pos_of_ne_zero hM
  obtain ⟨hM53, hrange⟩ := decompose_spec x hx neg M e hd
  obtain ⟨hr1, hr2⟩ := hrange hM
  obtain ⟨hE, hE1⟩ := decimalExponent_spec M e hM0 hr1 hr2
  have hX1 : (10 : Rat) ^ decimalExponent M e ≤ (M : Rat) * 2 ^ e := (tenPowLe_rat _ _ _).mp hE
  have hX2 : (M : Rat) * 2 ^ e < (10 : Rat) ^ (decimalExponent M e + 1) := by
    apply Rat.not_le.mp
    intro h
    have := (tenPowLe_rat (decimalExponent M e + 1) M e).mpr h
    rw [this] at hE1
    cases hE1
  simp only [roundsTo_rat]
  generalize hlc : (decide (M = 2 ^ 52) && decide (e > -1074)) = lc
  generalize hincl : (M % 2 == 0) = incl
  generalize hbig : decimalExponent M e = big at hE hE1 hX1 hX2
  have hlo := roundingInterval_lo_lt M lc hM0 e
  have hhi := roundingInterval_hi_gt M lc e
  have hXpos : (0 : Rat) < (M : Rat) * 2 ^ e := Rat.mul_pos (natCast_pos' hM0) (two_zpow_pos e)
  have hlo0 : (0 : Rat) < ((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2) := by
    apply Rat.mul_pos _ (two_zpow_pos _)
    apply natCast_pos'
    unfold roundingInterval
    split <;> omega
  have h17 := candidate_seventeen M e hM hM53 big hE lc incl hlc
  have mono : ∀ p q : Nat, 1 ≤ p → p ≤ q → (candidate M e lc incl (big - p + 1)).isSome = true →
      (candidate M e lc incl (big - q + 1)).isSome = true := by
    intro p q hp hpq h
    obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
    induction d with
    | zero => exact h
    | succ d ih =>
      have := candidate_step hM0 _ (ih (by omega))
      rw [show big - ((p + d : Nat) : Int) + 1 - 1 = big - ((p + (d + 1) : Nat) : Int) + 1 by omega] at this
      exact this
  have hp := searchDigits_spec (fun p => (candidate M e lc incl (big - p + 1)).isSome) 5 1 17 h17
    (by decide) (by decide)
  have hpb := searchDigits_bounds (fun p => (candidate M e lc incl (big - p + 1)).isSome) 5 1 17 (by decide)
  have hleast := searchDigits_least (fun p => (candidate M e lc incl (big - p + 1)).isSome) 1 mono 5 1 17
    (Nat.le_refl 1) h17 (by decide) (by decide) (fun p h1 h2 => absurd h2 (by omega))
  unfold shortest
  simp only [hx, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hd]
  simp only [hM, ite_false, hlc, hincl, hbig]
  generalize searchDigits (fun p => (candidate M e lc incl (big - p + 1)).isSome) 5 1 17 = p at hp hpb hleast
  cases hc : candidate M e lc incl (big - p + 1) with
  | none => rw [hc] at hp; cases hp
  | some c =>
    simp only
    obtain ⟨j, hj1, hj2⟩ := stripZeros_spec 20 c (big - p + 1)
    have hnt0 := stripZeros_noTrailing 20 c (big - p + 1)
    generalize stripZeros 20 c (big - p + 1) = sd at hj1 hj2 hnt0
    obtain ⟨digits, exponent⟩ := sd
    simp only at hj1 hj2 hnt0
    refine ⟨_, rfl, rfl, ?_⟩
    simp only
    have hp1 : 1 ≤ p := hpb.1
    have hp17 : p ≤ 17 := hpb.2
    obtain ⟨hcin, hopt⟩ := candidate_best hM0 hc
    have hT := ten_zpow_pos (big - p + 1)
    obtain ⟨hn1, hn2⟩ := optimal_near hT hlo hhi hXpos hcin hopt
    have hcand1 : InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2)) (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2))
        incl (((1 : Nat) : Rat) * 10 ^ big) ∨
        InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2)) (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2))
        incl (((10 : Nat) : Rat) * 10 ^ big) → p = 1 := by
      intro h
      have hs : (candidate M e lc incl (big - (1 : Nat) + 1)).isSome = true := by
        rw [show big - ((1 : Nat) : Int) + 1 = big by omega]
        rcases h with h | h
        · exact candidate_isSome_of_InI hM0 h
        · exact candidate_isSome_of_InI hM0 h
      apply Classical.byContradiction
      intro hne
      have := hleast 1 (Nat.le_refl 1) (by omega)
      rw [this] at hs
      cases hs
    have hF2 : ∀ (m : Nat) (q : Int), m ≠ 0 → InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2))
        (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2)) incl ((m : Rat) * 10 ^ q) →
        p ≤ (Nat.toDigits 10 m).length ∧ (q ≠ big - (Nat.toDigits 10 m).length + 1 → p = 1) := by
      intro m q hm hin
      have hn := digits_length_pos m
      rcases placement hm hX1 hX2 hlo hhi hin with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · refine ⟨?_, fun hne => absurd h hne⟩
        by_cases hn17 : (Nat.toDigits 10 m).length ≤ 17
        · have hs : (candidate M e lc incl (big - ((Nat.toDigits 10 m).length : Nat) + 1)).isSome = true := by
            rw [← h]
            exact candidate_isSome_of_InI hM0 hin
          apply Classical.byContradiction
          intro hlt
          have := hleast _ hn (by omega)
          rw [this] at hs
          cases hs
        · omega
      · have := hcand1 (Or.inl h3); exact ⟨by omega, fun _ => this⟩
      · have := hcand1 (Or.inr h3); exact ⟨by omega, fun _ => this⟩
    have hnotie : InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2)) (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2))
        incl (((9 : Nat) : Rat) * 10 ^ (big - p + 1)) → 2 * ((M : Rat) * 2 ^ e) = 19 * 10 ^ (big - p + 1) → False :=
      fun h9 ht => no_tie hM0 h9 ht
    generalize ((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2) = lo at hlo hlo0 hcin hopt hcand1 hF2 hnotie ⊢
    generalize ((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2) = hi at hhi hcin hopt hcand1 hF2 hnotie ⊢
    generalize (M : Rat) * 2 ^ e = X at hX1 hX2 hXpos hlo hhi hopt hn1 hn2 hnotie ⊢
    have h10big : (10 : Rat) ^ big = ((10 ^ (p - 1) : Nat) : Rat) * 10 ^ (big - p + 1) := by
      rw [ten_pow_nat_zpow]; congr 1; omega
    have h10big1 : (10 : Rat) ^ (big + 1) = ((10 ^ p : Nat) : Rat) * 10 ^ (big - p + 1) := by
      rw [ten_pow_nat_zpow]; congr 1; omega
    have hc_ge : 10 ^ (p - 1) ≤ c := by
      have : ((10 ^ (p - 1) : Nat) : Rat) * 10 ^ (big - p + 1) < ((c + 1 : Nat) : Rat) * 10 ^ (big - p + 1) := by
        rw [natCast_succ_rat]; grind
      have := nat_lt_of_mul_lt hT this
      omega
    have hc_le : c ≤ 10 ^ p := by
      have : (c : Rat) * 10 ^ (big - p + 1) < ((10 ^ p + 1 : Nat) : Rat) * 10 ^ (big - p + 1) := by
        rw [natCast_succ_rat]; grind
      have := nat_lt_of_mul_lt hT this
      omega
    have hc0 : c ≠ 0 := by have := Nat.one_le_pow (p - 1) 10 (by decide); omega
    have hc20 : c < 10 ^ 20 := Nat.lt_of_le_of_lt hc_le (Nat.pow_lt_pow_right (by decide) (by omega))
    have hnt := hnt0 hc0 hc20
    have hdig0 : digits ≠ 0 := by
      intro h; rw [h, Nat.zero_mul] at hj1; exact hc0 hj1
    have hval : (digits : Rat) * 10 ^ exponent = (c : Rat) * 10 ^ (big - p + 1) := by
      rw [hj2, hj1, Rat.natCast_mul, Rat.mul_assoc, ten_pow_nat_zpow, Int.add_comm (j : Int)]
    have hDin : InI lo hi incl ((digits : Rat) * 10 ^ exponent) := by rw [hval]; exact hcin
    refine ⟨hDin, ?_⟩
    have hpD := (hF2 digits exponent hdig0 hDin).1
    have hdle : digits ≤ c := by
      rw [hj1]; exact Nat.le_mul_of_pos_right _ (Nat.pow_pos (by decide))
    have hdlt : digits < 10 ^ p := by
      rcases Nat.lt_or_ge digits (10 ^ p) with h | h
      · exact h
      · exfalso
        have hde : digits = 10 ^ p := by omega
        apply hnt
        rw [hde, show p = (p - 1) + 1 by omega, Nat.pow_succ]
        exact Nat.mul_mod_left _ _
    have hnD : (Nat.toDigits 10 digits).length = p := by
      have := (digits_length_le_iff digits p (by omega)).mpr hdlt
      omega
    have hdge : 10 ^ (p - 1) ≤ digits := by
      have := digits_ge digits hdig0
      rw [hnD] at this
      exact this
    have hj01 : j = 0 ∨ (j = 1 ∧ p = 1 ∧ digits = 1 ∧ c = 10) := by
      rcases (by omega : j = 0 ∨ j = 1 ∨ 2 ≤ j) with h | h | h
      · exact Or.inl h
      · right
        subst h
        have e1 : 10 ^ p = 10 ^ (p - 1) * 10 := by rw [← Nat.pow_succ]; congr 1; omega
        rw [Nat.pow_one] at hj1
        have hd : digits = 10 ^ (p - 1) := by
          generalize 10 ^ (p - 1) = A at hdge e1
          generalize 10 ^ p = B at hc_le e1
          omega
        have hp' : p = 1 := by
          apply Classical.byContradiction
          intro hne
          apply hnt
          rw [hd, show p - 1 = (p - 2) + 1 by omega, Nat.pow_succ]
          exact Nat.mul_mod_left _ _
        subst hp'
        refine ⟨rfl, rfl, by simpa using hd, by omega⟩
      · exfalso
        have h1 : 10 ^ (p - 1) * 10 ^ j ≤ c := by rw [hj1]; exact Nat.mul_le_mul_right _ hdge
        have h2 : 10 ^ (p - 1) * 10 ^ j = 10 ^ (p - 1 + j) := (Nat.pow_add _ _ _).symm
        have h3 : 10 ^ p < 10 ^ (p - 1 + j) := Nat.pow_lt_pow_right (by decide) (by omega)
        omega
    intro m q hin
    have hm0 : m ≠ 0 := by
      rintro rfl
      unfold InI at hin
      have : ((0 : Nat) : Rat) * 10 ^ q = 0 := by rw [show ((0 : Nat) : Rat) = 0 from rfl]; grind
      rw [this] at hin
      grind
    obtain ⟨hpn, hpq⟩ := hF2 m q hm0 hin
    rcases Nat.lt_or_ge p (Nat.toDigits 10 m).length with hlt | hge
    · left; rw [hnD]; exact hlt
    · right
      have hn : (Nat.toDigits 10 m).length = p := by omega
      refine ⟨by rw [hnD, hn], ?_⟩
      rw [hval]
      have hmlt := digits_lt m
      rw [hn] at hmlt
      by_cases hq : q = big - p + 1
      · subst hq
        rcases hopt m hin with h | ⟨h, h'⟩
        · exact Or.inl h
        · rcases hj01 with hj0 | ⟨-, hp', -, hc'⟩
          · subst hj0
            have hdc : digits = c := by rw [hj1]; simp
            right
            refine ⟨h, ?_⟩
            rcases h' with hmc | ⟨h1, h2⟩
            · left; exact ⟨hmc.trans hdc.symm, by omega⟩
            · right; exact ⟨by rw [hdc]; exact h1, h2⟩
          · exfalso
            subst hp' hc'
            rcases h' with hmc | ⟨-, hmodd⟩
            · omega
            · have hm9 : (m : Rat) ≤ 9 := by
                have : m ≤ 9 := by omega
                exact Rat.natCast_le_natCast.mpr this
              have hmT := Rat.mul_le_mul_of_nonneg_right hm9 (Rat.le_of_lt hT)
              have h10 : ((10 : Nat) : Rat) = 10 := rfl
              have h10' : ((10 ^ 1 : Nat) : Rat) = 10 := rfl
              rw [h10] at h hn2
              rw [h10'] at h10big1
              have hXT : X < 10 * 10 ^ (big - ((1 : Nat) : Int) + 1) := by grind
              have hXT9 : 9 * 10 ^ (big - ((1 : Nat) : Int) + 1) ≤ X := by grind
              rw [Rat.abs_of_nonneg (x := 10 * 10 ^ (big - ((1 : Nat) : Int) + 1) - X) (by grind),
                Rat.abs_of_nonpos (x := (m : Rat) * 10 ^ (big - ((1 : Nat) : Int) + 1) - X) (by grind)] at h
              have h2X : 2 * X = (10 + (m : Rat)) * 10 ^ (big - ((1 : Nat) : Int) + 1) := by grind
              have h17 : ((17 : Nat) : Rat) * 10 ^ (big - ((1 : Nat) : Int) + 1) <
                  ((10 + m : Nat) : Rat) * 10 ^ (big - ((1 : Nat) : Int) + 1) := by
                rw [Rat.natCast_add, h10, show ((17 : Nat) : Rat) = 17 from rfl]
                grind
              have h8 := nat_lt_of_mul_lt hT h17
              have hm9' : m = 9 := by omega
              subst hm9'
              apply hnotie hin
              rw [h2X]
              have : ((9 : Nat) : Rat) = 9 := rfl
              rw [this]
              grind
      · have hp' := hpq (by rw [hn]; exact hq)
        subst hp'
        have hk : big - ((1 : Nat) : Int) + 1 = big := by omega
        rw [hk] at hopt hn1 hn2 hval ⊢
        have h10' : ((10 ^ 1 : Nat) : Rat) = 10 := rfl
        rw [h10', hk] at h10big1
        rcases placement hm0 hX1 hX2 hlo hhi hin with h | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact absurd (by rw [h, hn]) hq
        · left
          have hb1 : ((1 : Nat) : Rat) = 1 := rfl
          rcases hopt 1 h3 with h | ⟨h, -⟩
          · rw [hb1, Rat.abs_of_nonpos (x := 1 * 10 ^ big - X) (by grind)] at h
            rw [Rat.abs_of_nonpos (x := (m : Rat) * 10 ^ q - X) (by grind)]
            grind
          · rw [hb1, Rat.abs_of_nonpos (x := 1 * 10 ^ big - X) (by grind)] at h
            rw [Rat.abs_of_nonpos (x := (m : Rat) * 10 ^ q - X) (by grind)]
            grind
        · have h10 : ((10 : Nat) : Rat) = 10 := rfl
          rcases hopt 10 h3 with h | ⟨h, h'⟩
          · left
            rw [h10, Rat.abs_of_nonneg (x := 10 * 10 ^ big - X) (by grind)] at h
            rw [Rat.abs_of_nonneg (x := (m : Rat) * 10 ^ q - X) (by grind)]
            grind
          · have hc10 : c = 10 := by
              rcases h' with h' | ⟨-, h'⟩
              · exact h'.symm
              · simp at h'
            rcases hj01 with hj0 | ⟨hj1', -, hd1, -⟩
            · exfalso
              subst hj0
              apply hnt
              rw [show digits = c by rw [hj1]; simp, hc10]
            · rw [h10, Rat.abs_of_nonneg (x := 10 * 10 ^ big - X) (by grind)] at h
              by_cases hlt' : 10 * 10 ^ big < (m : Rat) * 10 ^ q
              · left
                rw [Rat.abs_of_nonneg (x := (m : Rat) * 10 ^ q - X) (by grind)]
                grind
              · right
                have heq : (m : Rat) * 10 ^ q = 10 * 10 ^ big := by
                  rcases Rat.le_iff_lt_or_eq.mp (Rat.not_lt.mp hlt') with h4 | h4
                  · grind
                  · exact h4
                have hq1 : q = big + 1 := by
                  rw [hn] at h1
                  rcases (by omega : q = big + 1 ∨ big + 2 ≤ q) with h5 | h5
                  · exact h5
                  · exfalso
                    have e1 := ten_zpow_le h5
                    have e2 : (10 : Rat) ^ (big + 2) = 10 * (10 * 10 ^ big) := by
                      rw [show big + 2 = (big + 1) + 1 by omega, ten_zpow_succ, ten_zpow_succ]; grind
                    have hm1 : (1 : Rat) ≤ m := Rat.natCast_le_natCast.mpr (by omega : 1 ≤ m)
                    have e3 := Rat.mul_le_mul_of_nonneg_right hm1 (Rat.le_of_lt (ten_zpow_pos q))
                    have hpos := ten_zpow_pos big
                    grind
                have hm1 : m = 1 := by
                  subst hq1
                  have hne : (10 : Rat) ^ (big + 1) ≠ 0 := fun h5 => by
                    have := ten_zpow_pos (big + 1); rw [h5] at this; exact Rat.lt_irrefl this
                  have e : (m : Rat) * 10 ^ (big + 1) = 1 * 10 ^ (big + 1) := by
                    rw [heq, ten_zpow_succ]; grind
                  have : (m : Rat) = ((1 : Nat) : Rat) := by
                    calc (m : Rat) = m * 10 ^ (big + 1) * (10 ^ (big + 1))⁻¹ := by
                          rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hne, Rat.mul_one]
                      _ = 1 * 10 ^ (big + 1) * (10 ^ (big + 1))⁻¹ := by rw [e]
                      _ = ((1 : Nat) : Rat) := by
                          rw [Rat.mul_assoc, Rat.mul_inv_cancel _ hne, Rat.mul_one]; rfl
                  exact Rat.natCast_inj.mp this
                refine ⟨by rw [Rat.abs_of_nonneg (x := (m : Rat) * 10 ^ q - X) (by grind)]; grind, Or.inl ⟨?_, ?_⟩⟩
                · rw [hd1, hm1]
                · rw [hj2, hj1', hq1]; omega

end FloatText

end ExactJSON
