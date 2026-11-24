module

public import ExactJSON.OfScientific

public section

namespace ExactJSON

namespace FloatText

theorem rat_two_ne : (2 : Rat) ≠ 0 := by decide

theorem rat_ten_ne : (10 : Rat) ≠ 0 := by decide

theorem natCast_pow_rat (a n : Nat) : ((a ^ n : Nat) : Rat) = (a : Rat) ^ (n : Int) := by
  rw [Rat.natCast_pow, Rat.zpow_natCast]

theorem powSplit_rat (a : Nat) (ha : 0 < a) (k : Int) :
    ((powSplit a k).1 : Rat) = (a : Rat) ^ k * ((powSplit a k).2 : Rat) := by
  have ha' : (a : Rat) ≠ 0 := by
    intro h
    have : ((a : Nat) : Rat) = ((0 : Nat) : Rat) := by rw [h]; rfl
    have := Rat.natCast_inj.mp this
    omega
  unfold powSplit
  split
  · rename_i hk
    rw [natCast_pow_rat, Int.toNat_of_nonneg hk]
    simp
  · rename_i hk
    rw [natCast_pow_rat, Int.toNat_of_nonneg (by omega), ← Rat.zpow_add ha', Int.add_right_neg,
      Rat.zpow_zero]
    simp

theorem natCast_pos' {n : Nat} (h : 0 < n) : (0 : Rat) < (n : Rat) := Rat.natCast_pos.mpr h

theorem cross_lt {A B : Nat} {r t : Rat} (hA : 0 < A) (hr : 0 < r) (h : (B : Rat) * r = (A : Rat) * t)
    (u v : Nat) : u * A < v * B ↔ (u : Rat) * r < (v : Rat) * t := by
  have hA' := natCast_pos' hA
  constructor
  · intro huv
    have h1 : ((u * A : Nat) : Rat) < ((v * B : Nat) : Rat) := Rat.natCast_lt_natCast.mpr huv
    rw [Rat.natCast_mul, Rat.natCast_mul] at h1
    have h2 := Rat.mul_lt_mul_of_pos_right h1 hr
    apply (Rat.mul_lt_mul_right hA').mp
    calc (u : Rat) * r * A = u * A * r := by grind
      _ < v * B * r := h2
      _ = v * t * A := by grind
  · intro huv
    have h2 := Rat.mul_lt_mul_of_pos_right huv hA'
    have h3 : (u : Rat) * A * r < v * B * r := by
      calc (u : Rat) * A * r = u * r * A := by grind
        _ < v * t * A := h2
        _ = v * B * r := by grind
    have h4 := (Rat.mul_lt_mul_right hr).mp h3
    rw [← Rat.natCast_mul, ← Rat.natCast_mul] at h4
    exact Rat.natCast_lt_natCast.mp h4

theorem cross_lt' {A B : Nat} {r t : Rat} (hA : 0 < A) (hr : 0 < r) (h : (B : Rat) * r = (A : Rat) * t)
    (u v : Nat) : v * B < u * A ↔ (v : Rat) * t < (u : Rat) * r := by
  have hA' := natCast_pos' hA
  constructor
  · intro huv
    have h1 : ((v * B : Nat) : Rat) < ((u * A : Nat) : Rat) := Rat.natCast_lt_natCast.mpr huv
    rw [Rat.natCast_mul, Rat.natCast_mul] at h1
    have h2 := Rat.mul_lt_mul_of_pos_right h1 hr
    apply (Rat.mul_lt_mul_right hA').mp
    calc (v : Rat) * t * A = v * B * r := by grind
      _ < u * A * r := h2
      _ = u * r * A := by grind
  · intro huv
    have h2 := Rat.mul_lt_mul_of_pos_right huv hA'
    have h3 : (v : Rat) * B * r < u * A * r := by
      calc (v : Rat) * B * r = v * t * A := by grind
        _ < u * r * A := h2
        _ = u * A * r := by grind
    have h4 := (Rat.mul_lt_mul_right hr).mp h3
    rw [← Rat.natCast_mul, ← Rat.natCast_mul] at h4
    exact Rat.natCast_lt_natCast.mp h4

theorem cross_eq {A B : Nat} {r t : Rat} (hA : 0 < A) (hr : 0 < r) (h : (B : Rat) * r = (A : Rat) * t)
    (u v : Nat) : u * A = v * B ↔ (u : Rat) * r = (v : Rat) * t := by
  have hA' := natCast_pos' hA
  constructor
  · intro huv
    have h1 : ((u * A : Nat) : Rat) = ((v * B : Nat) : Rat) := by rw [huv]
    rw [Rat.natCast_mul, Rat.natCast_mul] at h1
    have h2 : (u : Rat) * r * A = v * t * A := by
      calc (u : Rat) * r * A = u * A * r := by grind
        _ = v * B * r := by rw [h1]
        _ = v * t * A := by grind
    have hne : (A : Rat) ≠ 0 := fun h0 => by rw [h0] at hA'; exact Rat.lt_irrefl hA'
    calc (u : Rat) * r = u * r * A * (A : Rat)⁻¹ := by
          rw [Rat.mul_assoc _ (A : Rat), Rat.mul_inv_cancel _ hne, Rat.mul_one]
      _ = v * t * A * (A : Rat)⁻¹ := by rw [h2]
      _ = v * t := by rw [Rat.mul_assoc _ (A : Rat), Rat.mul_inv_cancel _ hne, Rat.mul_one]
  · intro huv
    have hrne : r ≠ 0 := fun h0 => by rw [h0] at hr; exact Rat.lt_irrefl hr
    have h3 : (u : Rat) * A * r = v * B * r := by
      calc (u : Rat) * A * r = u * r * A := by grind
        _ = v * t * A := by rw [huv]
        _ = v * B * r := by grind
    have h4 : (u : Rat) * A = v * B := by
      calc (u : Rat) * A = u * A * r * r⁻¹ := by
            rw [Rat.mul_assoc _ r, Rat.mul_inv_cancel _ hrne, Rat.mul_one]
        _ = v * B * r * r⁻¹ := by rw [h3]
        _ = v * B := by rw [Rat.mul_assoc _ r, Rat.mul_inv_cancel _ hrne, Rat.mul_one]
    rw [← Rat.natCast_mul, ← Rat.natCast_mul] at h4
    exact Rat.natCast_inj.mp h4

theorem scale_rat (e k : Int) :
    ((scale e k).2 : Rat) * (2 : Rat) ^ (e - 2) = ((scale e k).1 : Rat) * (10 : Rat) ^ k := by
  rw [scale_eq]
  simp only [Rat.natCast_mul]
  have h2 := powSplit_rat 2 (by decide) (e - 2)
  have h10 := powSplit_rat 10 (by decide) k
  simp only [show ((2 : Nat) : Rat) = 2 from rfl, show ((10 : Nat) : Rat) = 10 from rfl] at h2 h10
  rw [h2, h10]
  grind

theorem two_zpow_pos (e : Int) : (0 : Rat) < (2 : Rat) ^ e := Rat.zpow_pos (by decide)

theorem ten_zpow_pos (e : Int) : (0 : Rat) < (10 : Rat) ^ e := Rat.zpow_pos (by decide)

@[expose] def InI (lo hi : Rat) (incl : Bool) (v : Rat) : Prop :=
  (lo < v ∨ (incl = true ∧ lo = v)) ∧ (v < hi ∨ (incl = true ∧ v = hi))

theorem fits_rat (low high : Nat) (e k : Int) (incl : Bool) (d : Nat) :
    fits low high (scale e k).1 (scale e k).2 incl d = true ↔
      InI ((low : Rat) * (2 : Rat) ^ (e - 2)) ((high : Rat) * (2 : Rat) ^ (e - 2)) incl ((d : Rat) * (10 : Rat) ^ k) := by
  have hA := scale_fst_pos e k
  have hr := two_zpow_pos (e - 2)
  have hs := scale_rat e k
  have l1 := cross_lt hA hr hs low d
  have l2 := cross_lt' hA hr hs high d
  have l3 := cross_eq hA hr hs low d
  have l4 := cross_eq hA hr hs high d
  unfold fits InI
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [l1, l2, l3, show d * (scale e k).2 = high * (scale e k).1 ↔ (d : Rat) * 10 ^ k = high * 2 ^ (e - 2) by
    rw [eq_comm, l4, eq_comm]]

theorem rat_le_iff_mul {a b c : Rat} (hc : 0 < c) : a ≤ b ↔ a * c ≤ b * c :=
  ⟨fun h => Rat.mul_le_mul_of_nonneg_right h (Rat.le_of_lt hc), fun h => Rat.le_of_mul_le_mul_right h hc⟩

theorem tenPowLe_rat (k : Int) (m : Nat) (e : Int) :
    tenPowLe k m e = true ↔ (10 : Rat) ^ k ≤ (m : Rat) * (2 : Rat) ^ e := by
  unfold tenPowLe
  simp only [decide_eq_true_eq]
  have h10 := powSplit_rat 10 (by decide) k
  have h2 := powSplit_rat 2 (by decide) e
  have p10 := powSplit_pos 10 (by decide) k
  have p2 := powSplit_pos 2 (by decide) e
  simp only [show ((2 : Nat) : Rat) = 2 from rfl, show ((10 : Nat) : Rat) = 10 from rfl] at h2 h10
  generalize powSplit 10 k = t at h10 p10
  generalize powSplit 2 e = b at h2 p2
  obtain ⟨tn, td⟩ := t
  obtain ⟨bn, bd⟩ := b
  simp only at h10 h2 p10 p2 ⊢
  have hpos : (0 : Rat) < (td : Rat) * bd := Rat.mul_pos (natCast_pos' p10.2) (natCast_pos' p2.2)
  rw [← Rat.natCast_le_natCast, Rat.natCast_mul, Rat.natCast_mul, Rat.natCast_mul, h10, h2]
  constructor
  · intro h
    apply (rat_le_iff_mul hpos).mpr
    calc (10 : Rat) ^ k * (td * bd) = 10 ^ k * td * bd := by grind
      _ ≤ m * (2 ^ e * bd) * td := h
      _ = m * 2 ^ e * (td * bd) := by grind
  · intro h
    have h' := (rat_le_iff_mul hpos).mp h
    calc (10 : Rat) ^ k * td * bd = 10 ^ k * (td * bd) := by grind
      _ ≤ m * 2 ^ e * (td * bd) := h'
      _ = m * (2 ^ e * bd) * td := by grind

theorem two_zpow_sub_two (e : Int) : (2 : Rat) ^ e = 4 * (2 : Rat) ^ (e - 2) := by
  have := Rat.zpow_add rat_two_ne (e - 2) 2
  rw [show e - 2 + 2 = e by omega] at this
  rw [this]
  have h4 : (2 : Rat) ^ (2 : Int) = 4 := by decide
  rw [h4]
  grind

theorem InI_convex {lo hi X y z : Rat} {incl : Bool} (hy : InI lo hi incl y) (hlo : lo < X) (hhi : X < hi)
    (hz : (y ≤ z ∧ z ≤ X) ∨ (X ≤ z ∧ z ≤ y)) : InI lo hi incl z := by
  unfold InI at hy ⊢
  grind

theorem rat_lt_trichotomy (a b : Rat) : a < b ∨ a = b ∨ b < a := by
  rcases Rat.le_total (a := a) (b := b) with h | h
  · rcases (Rat.le_iff_lt_or_eq.mp h) with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases (Rat.le_iff_lt_or_eq.mp h) with h | h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h.symm)

theorem natCast_succ_rat (n : Nat) : ((n + 1 : Nat) : Rat) = (n : Rat) + 1 := by
  rw [Rat.natCast_add]
  rfl

theorem best_abstract {X T lo hi : Rat} {incl : Bool} {d0 c : Nat} (hT : 0 < T)
    (h0 : (d0 : Rat) * T ≤ X) (h1 : X < ((d0 : Rat) + 1) * T) (hlo : lo < X) (hhi : X < hi)
    (hc : (InI lo hi incl ((d0 : Rat) * T) ∧ InI lo hi incl (((d0 : Rat) + 1) * T) ∧
        (2 * X < (2 * (d0 : Rat) + 1) * T → c = d0) ∧ ((2 * (d0 : Rat) + 1) * T < 2 * X → c = d0 + 1) ∧
        (2 * X = (2 * (d0 : Rat) + 1) * T → c = if d0 % 2 = 0 then d0 else d0 + 1)) ∨
      (InI lo hi incl ((d0 : Rat) * T) ∧ ¬ InI lo hi incl (((d0 : Rat) + 1) * T) ∧ c = d0) ∨
      (¬ InI lo hi incl ((d0 : Rat) * T) ∧ InI lo hi incl (((d0 : Rat) + 1) * T) ∧ c = d0 + 1)) :
    InI lo hi incl ((c : Rat) * T) ∧ ∀ y : Nat, InI lo hi incl ((y : Rat) * T) →
      ((c : Rat) * T - X).abs < ((y : Rat) * T - X).abs ∨
      (((c : Rat) * T - X).abs = ((y : Rat) * T - X).abs ∧ (y = c ∨ (c % 2 = 0 ∧ y % 2 = 1))) := by
  have e0 : ((d0 : Rat) * T - X).abs = X - d0 * T := by
    rw [Rat.abs_of_nonpos (by grind)]; grind
  have e1 : (((d0 : Rat) + 1) * T - X).abs = (d0 + 1) * T - X := by
    rw [Rat.abs_of_nonneg (by grind)]
  have hd1 := natCast_succ_rat d0
  have key : InI lo hi incl ((c : Rat) * T) ∧
      (InI lo hi incl ((d0 : Rat) * T) → ((c : Rat) * T - X).abs ≤ X - d0 * T) ∧
      (InI lo hi incl (((d0 : Rat) + 1) * T) → ((c : Rat) * T - X).abs ≤ (d0 + 1) * T - X) ∧
      (InI lo hi incl ((d0 : Rat) * T) → ((c : Rat) * T - X).abs = X - d0 * T →
        c = d0 ∨ (c % 2 = 0 ∧ d0 % 2 = 1)) ∧
      (InI lo hi incl (((d0 : Rat) + 1) * T) → ((c : Rat) * T - X).abs = (d0 + 1) * T - X →
        c = d0 + 1 ∨ (c % 2 = 0 ∧ (d0 + 1) % 2 = 1)) := by
    rcases hc with ⟨f0, f1, c1, c2, c3⟩ | ⟨f0, f1, rfl⟩ | ⟨f0, f1, rfl⟩
    · rcases rat_lt_trichotomy (2 * X) ((2 * (d0 : Rat) + 1) * T) with hl | he | hg
      · have := c1 hl
        subst this
        refine ⟨f0, fun _ => by rw [e0]; exact Rat.le_refl, fun _ => by rw [e0]; grind,
          fun _ _ => Or.inl rfl, fun _ h => by rw [e0] at h; grind⟩
      · have hcv := c3 he
        by_cases hpar : d0 % 2 = 0
        · simp only [hpar, ↓reduceIte] at hcv
          subst hcv
          refine ⟨f0, fun _ => by rw [e0]; exact Rat.le_refl, fun _ => by rw [e0]; grind,
            fun _ _ => Or.inl rfl, fun _ _ => Or.inr ⟨hpar, by omega⟩⟩
        · simp only [hpar, ↓reduceIte] at hcv
          subst hcv
          rw [hd1]
          refine ⟨f1, fun _ => by rw [e1]; grind, fun _ => by rw [e1]; exact Rat.le_refl,
            fun _ _ => Or.inr ⟨by omega, by omega⟩, fun _ _ => Or.inl rfl⟩
      · have := c2 hg
        subst this
        rw [hd1]
        refine ⟨f1, fun _ => by rw [e1]; grind, fun _ => by rw [e1]; exact Rat.le_refl,
          fun _ h => by rw [e1] at h; grind, fun _ _ => Or.inl rfl⟩
    · refine ⟨f0, fun _ => by rw [e0]; exact Rat.le_refl, fun h => absurd h f1,
        fun _ _ => Or.inl rfl, fun h => absurd h f1⟩
    · rw [hd1]
      refine ⟨f1, fun h => absurd h f0, fun _ => by rw [e1]; exact Rat.le_refl,
        fun h => absurd h f0, fun _ _ => Or.inl rfl⟩
  refine ⟨key.1, fun y hy => ?_⟩
  rcases (by omega : y < d0 ∨ y = d0 ∨ y = d0 + 1 ∨ d0 + 1 < y) with hy' | rfl | rfl | hy'
  · have hyc : (y : Rat) + 1 ≤ d0 := by
      rw [← natCast_succ_rat]; exact Rat.natCast_le_natCast.mpr hy'
    have hyT : (y : Rat) * T + T ≤ d0 * T := by
      have := Rat.mul_le_mul_of_nonneg_right hyc (Rat.le_of_lt hT)
      grind
    have hF0 : InI lo hi incl ((d0 : Rat) * T) := InI_convex hy hlo hhi (Or.inl ⟨by grind, h0⟩)
    have ey : ((y : Rat) * T - X).abs = X - y * T := by
      rw [Rat.abs_of_nonpos (by grind)]; grind
    left
    rw [ey]
    have := key.2.1 hF0
    grind
  · rcases Rat.le_iff_lt_or_eq.mp (key.2.1 hy) with hl | he
    · left; rw [e0]; exact hl
    · right; rw [e0]; exact ⟨he, (key.2.2.2.1 hy he).imp Eq.symm id⟩
  · rw [hd1] at hy ⊢
    rcases Rat.le_iff_lt_or_eq.mp (key.2.2.1 hy) with hl | he
    · left; rw [e1]; exact hl
    · right; rw [e1]; exact ⟨he, (key.2.2.2.2 hy he).imp Eq.symm id⟩
  · have hyc : (d0 : Rat) + 1 + 1 ≤ y := by
      rw [← natCast_succ_rat, ← natCast_succ_rat]; exact Rat.natCast_le_natCast.mpr hy'
    have hyT : ((d0 : Rat) + 1) * T + T ≤ y * T := by
      have := Rat.mul_le_mul_of_nonneg_right hyc (Rat.le_of_lt hT)
      grind
    have hF1 : InI lo hi incl (((d0 : Rat) + 1) * T) := InI_convex hy hlo hhi (Or.inr ⟨by grind, by grind⟩)
    have ey : ((y : Rat) * T - X).abs = y * T - X := by
      rw [Rat.abs_of_nonneg (by grind)]
    left
    rw [ey]
    have := key.2.2.1 hF1
    grind

theorem scale_snd_pos (e k : Int) : 0 < (scale e k).2 := by
  rw [scale_eq]
  exact Nat.mul_pos (powSplit_pos 2 (by decide) _).2 (powSplit_pos 10 (by decide) _).1

theorem roundingInterval_mid (M : Nat) (lc : Bool) : (roundingInterval M lc).2.1 = 4 * M := rfl

theorem cross_le' {A B : Nat} {r t : Rat} (hA : 0 < A) (hr : 0 < r) (h : (B : Rat) * r = (A : Rat) * t)
    (u v : Nat) : v * B ≤ u * A ↔ (v : Rat) * t ≤ (u : Rat) * r := by
  rw [← Nat.not_lt, cross_lt hA hr h u v, Rat.not_lt]

theorem four_mul_two_zpow (M : Nat) (e : Int) :
    (((4 * M : Nat) : Rat)) * (2 : Rat) ^ (e - 2) = (M : Rat) * (2 : Rat) ^ e := by
  rw [two_zpow_sub_two e, Rat.natCast_mul]
  have : ((4 : Nat) : Rat) = 4 := rfl
  rw [this]
  grind

theorem eight_mul_two_zpow (M : Nat) (e : Int) :
    (((8 * M : Nat) : Rat)) * (2 : Rat) ^ (e - 2) = 2 * ((M : Rat) * (2 : Rat) ^ e) := by
  rw [two_zpow_sub_two e, Rat.natCast_mul]
  have : ((8 : Nat) : Rat) = 8 := rfl
  rw [this]
  grind

theorem two_mul_succ_rat (d : Nat) : ((2 * d + 1 : Nat) : Rat) = 2 * (d : Rat) + 1 := by
  rw [natCast_succ_rat, Rat.natCast_mul]
  rfl

theorem roundingInterval_lo_lt (M : Nat) (lc : Bool) (hM : 0 < M) (e : Int) :
    ((roundingInterval M lc).1 : Rat) * (2 : Rat) ^ (e - 2) < (M : Rat) * (2 : Rat) ^ e := by
  rw [← four_mul_two_zpow M e]
  apply Rat.mul_lt_mul_of_pos_right _ (two_zpow_pos _)
  apply Rat.natCast_lt_natCast.mpr
  unfold roundingInterval
  split <;> omega

theorem roundingInterval_hi_gt (M : Nat) (lc : Bool) (e : Int) :
    (M : Rat) * (2 : Rat) ^ e < ((roundingInterval M lc).2.2 : Rat) * (2 : Rat) ^ (e - 2) := by
  rw [← four_mul_two_zpow M e]
  apply Rat.mul_lt_mul_of_pos_right _ (two_zpow_pos _)
  apply Rat.natCast_lt_natCast.mpr
  unfold roundingInterval
  simp only
  omega

theorem candidate_best {M : Nat} {e : Int} {lc incl : Bool} {k : Int} {c : Nat} (hM : 0 < M)
    (h : candidate M e lc incl k = some c) :
    InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2)) (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2))
        incl ((c : Rat) * 10 ^ k) ∧
      ∀ y : Nat, InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2))
          (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2)) incl ((y : Rat) * 10 ^ k) →
        ((c : Rat) * 10 ^ k - (M : Rat) * 2 ^ e).abs < ((y : Rat) * 10 ^ k - (M : Rat) * 2 ^ e).abs ∨
        (((c : Rat) * 10 ^ k - (M : Rat) * 2 ^ e).abs = ((y : Rat) * 10 ^ k - (M : Rat) * 2 ^ e).abs ∧
          (y = c ∨ (c % 2 = 0 ∧ y % 2 = 1))) := by
  have ha := scale_fst_pos e k
  have hb := scale_snd_pos e k
  have hr := two_zpow_pos (e - 2)
  have hs := scale_rat e k
  have hT := ten_zpow_pos k
  have hX4 := four_mul_two_zpow M e
  have hX8 := eight_mul_two_zpow M e
  unfold candidate at h
  simp only [roundingInterval_mid] at h
  obtain ⟨d0, hd0⟩ : ∃ d0, 4 * M * (scale e k).1 / (scale e k).2 = d0 := ⟨_, rfl⟩
  simp only [hd0] at h
  have hdiv : d0 * (scale e k).2 ≤ 4 * M * (scale e k).1 := hd0 ▸ Nat.div_mul_le_self _ _
  have hQ1 : (d0 + 1) * (scale e k).2 = d0 * (scale e k).2 + (scale e k).2 := Nat.succ_mul _ _
  have hlt : 4 * M * (scale e k).1 < (d0 + 1) * (scale e k).2 := by
    have := Nat.lt_div_mul_add (a := 4 * M * (scale e k).1) hb
    rw [hd0] at this
    rw [hQ1]
    exact this
  have r0 : (d0 : Rat) * 10 ^ k ≤ (M : Rat) * 2 ^ e := by
    rw [← hX4]
    exact (cross_le' ha hr hs (4 * M) d0).mp hdiv
  have r1 : (M : Rat) * 2 ^ e < ((d0 : Rat) + 1) * 10 ^ k := by
    rw [← hX4, ← natCast_succ_rat]
    exact (cross_lt ha hr hs (4 * M) (d0 + 1)).mp hlt
  have hP8 : 8 * M * (scale e k).1 = 2 * (4 * M * (scale e k).1) := by
    rw [show 8 * M = 2 * (4 * M) by omega, Nat.mul_assoc]
  have hQ2 : (2 * d0 + 1) * (scale e k).2 = 2 * (d0 * (scale e k).2) + (scale e k).2 := by
    rw [Nat.succ_mul, Nat.mul_assoc]
  have c1 := cross_lt ha hr hs (8 * M) (2 * d0 + 1)
  have c2 := cross_lt' ha hr hs (8 * M) (2 * d0 + 1)
  have c3 := cross_eq ha hr hs (8 * M) (2 * d0 + 1)
  rw [hP8, hQ2, hX8, two_mul_succ_rat] at c1 c2 c3
  have f0 := fits_rat (roundingInterval M lc).1 (roundingInterval M lc).2.2 e k incl d0
  have f1 := fits_rat (roundingInterval M lc).1 (roundingInterval M lc).2.2 e k incl (d0 + 1)
  rw [natCast_succ_rat] at f1
  rw [hQ1] at hlt h
  generalize 4 * M * (scale e k).1 = P at hdiv hlt c1 c2 c3 h
  generalize d0 * (scale e k).2 = Q at hdiv hlt c1 c2 c3 h
  have t1 : P - Q < Q + (scale e k).2 - P ↔ 2 * ((M : Rat) * 2 ^ e) < (2 * (d0 : Rat) + 1) * 10 ^ k := by
    rw [← c1]; omega
  have t2 : Q + (scale e k).2 - P < P - Q ↔ (2 * (d0 : Rat) + 1) * 10 ^ k < 2 * ((M : Rat) * 2 ^ e) := by
    rw [← c2]; omega
  have t3 : ¬ (P - Q < Q + (scale e k).2 - P) → ¬ (Q + (scale e k).2 - P < P - Q) →
      2 * ((M : Rat) * 2 ^ e) = (2 * (d0 : Rat) + 1) * 10 ^ k := by
    intro n1 n2
    rw [← c3]
    omega
  apply best_abstract hT r0 r1 (roundingInterval_lo_lt M lc hM e) (roundingInterval_hi_gt M lc e)
  split at h
  · rename_i h0 h1
    left
    refine ⟨f0.mp h0, f1.mp h1, fun hh => ?_, fun hh => ?_, fun hh => ?_⟩
    · simp only [t1.mpr hh, ↓reduceIte, Option.some.injEq] at h
      exact h.symm
    · have n1 : ¬ (P - Q < Q + (scale e k).2 - P) := fun h' => by have := t1.mp h'; grind
      simp only [n1, t2.mpr hh, ↓reduceIte, Option.some.injEq] at h
      exact h.symm
    · have n1 : ¬ (P - Q < Q + (scale e k).2 - P) := fun h' => by have := t1.mp h'; grind
      have n2 : ¬ (Q + (scale e k).2 - P < P - Q) := fun h' => by have := t2.mp h'; grind
      simp only [n1, n2, ↓reduceIte] at h
      by_cases hp : d0 % 2 = 0
      · simp only [hp, BEq.rfl, ↓reduceIte, Option.some.injEq] at h
        simp only [hp, ↓reduceIte]
        exact h.symm
      · have : (d0 % 2 == 0) = false := by simpa using hp
        simp only [this, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        simp only [hp, ↓reduceIte]
        exact h.symm
  · rename_i h0 h1
    right; left
    have nf1 : ¬ InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2))
        (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2)) incl (((d0 : Rat) + 1) * 10 ^ k) := by
      intro hh
      have := f1.mpr hh
      rw [this] at h1
      cases h1
    exact ⟨f0.mp h0, nf1, (Option.some.inj h).symm⟩
  · rename_i h0 h1
    right; right
    have nf0 : ¬ InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2))
        (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2)) incl ((d0 : Rat) * 10 ^ k) := by
      intro hh
      have := f0.mpr hh
      rw [this] at h0
      cases h0
    exact ⟨nf0, f1.mp h1, (Option.some.inj h).symm⟩
  · cases h

theorem digits_length_pos (m : Nat) : 1 ≤ (Nat.toDigits 10 m).length :=
  List.length_pos_iff.mpr Nat.toDigits_ne_nil

theorem digits_lt (m : Nat) : m < 10 ^ (Nat.toDigits 10 m).length :=
  (Nat.length_toDigits_le_iff (by decide) (digits_length_pos m)).mp (Nat.le_refl _)

theorem digits_ge (m : Nat) (hm : m ≠ 0) : 10 ^ ((Nat.toDigits 10 m).length - 1) ≤ m := by
  generalize hn : (Nat.toDigits 10 m).length = n
  have hn1 : 1 ≤ n := hn ▸ digits_length_pos m
  by_cases hn2 : n = 1
  · subst hn2; simp; omega
  · have := mt (Nat.length_toDigits_le_iff (b := 10) (n := m) (k := n - 1) (by decide) (by omega)).mpr (by omega)
    omega

theorem digits_length_le_iff (m n : Nat) (hn : 0 < n) : (Nat.toDigits 10 m).length ≤ n ↔ m < 10 ^ n :=
  Nat.length_toDigits_le_iff (by decide) hn

theorem ten_zpow_le {a b : Int} (h : a ≤ b) : (10 : Rat) ^ a ≤ (10 : Rat) ^ b := by
  have hb : b = a + ((b - a).toNat : Nat) := by omega
  rw [hb, Rat.zpow_add rat_ten_ne, Rat.zpow_natCast]
  have h1 : (1 : Rat) ≤ (10 : Rat) ^ (b - a).toNat := by
    have : 1 ≤ 10 ^ (b - a).toNat := Nat.one_le_pow _ _ (by decide)
    have := Rat.natCast_le_natCast.mpr this
    rw [Rat.natCast_pow] at this
    exact this
  have := Rat.mul_le_mul_of_nonneg_left h1 (Rat.le_of_lt (ten_zpow_pos a))
  grind

theorem ten_zpow_succ (a : Int) : (10 : Rat) ^ (a + 1) = (10 : Rat) ^ a * 10 := Rat.zpow_add_one rat_ten_ne a

theorem ten_pow_nat_zpow (n : Nat) (q : Int) :
    ((10 ^ n : Nat) : Rat) * (10 : Rat) ^ q = (10 : Rat) ^ ((n : Int) + q) := by
  rw [natCast_pow_rat, Rat.zpow_add rat_ten_ne]
  rfl

theorem placement {lo hi X : Rat} {incl : Bool} {m : Nat} {q big : Int} (hm : m ≠ 0)
    (hX1 : (10 : Rat) ^ big ≤ X) (hX2 : X < (10 : Rat) ^ (big + 1)) (hlo : lo < X) (hhi : X < hi)
    (hin : InI lo hi incl ((m : Rat) * 10 ^ q)) :
    q = big - (Nat.toDigits 10 m).length + 1 ∨
      (q < big - (Nat.toDigits 10 m).length + 1 ∧ (m : Rat) * 10 ^ q < 10 ^ big ∧
        InI lo hi incl (((1 : Nat) : Rat) * 10 ^ big)) ∨
      (big - (Nat.toDigits 10 m).length + 1 < q ∧ (10 : Rat) ^ (big + 1) ≤ (m : Rat) * 10 ^ q ∧
        InI lo hi incl (((10 : Nat) : Rat) * 10 ^ big)) := by
  have hn1 := digits_length_pos m
  have hlt := digits_lt m
  have hge := digits_ge m hm
  generalize (Nat.toDigits 10 m).length = n at hn1 hlt hge ⊢
  rcases (by omega : q = big - n + 1 ∨ q < big - n + 1 ∨ big - n + 1 < q) with h | h | h
  · exact Or.inl h
  · right; left
    have e1 : (m : Rat) * 10 ^ q < ((10 ^ n : Nat) : Rat) * 10 ^ q :=
      Rat.mul_lt_mul_of_pos_right (Rat.natCast_lt_natCast.mpr hlt) (ten_zpow_pos q)
    rw [ten_pow_nat_zpow] at e1
    have e2 := ten_zpow_le (show (n : Int) + q ≤ big by omega)
    have e3 : (m : Rat) * 10 ^ q < 10 ^ big := by grind
    refine ⟨h, e3, InI_convex hin hlo hhi (Or.inl ⟨by grind, by grind⟩)⟩
  · right; right
    have e1 : ((10 ^ (n - 1) : Nat) : Rat) * 10 ^ q ≤ (m : Rat) * 10 ^ q :=
      Rat.mul_le_mul_of_nonneg_right (Rat.natCast_le_natCast.mpr hge) (Rat.le_of_lt (ten_zpow_pos q))
    rw [ten_pow_nat_zpow] at e1
    have e2 := ten_zpow_le (show big + 1 ≤ ((n - 1 : Nat) : Int) + q by omega)
    have e3 : (10 : Rat) ^ (big + 1) ≤ (m : Rat) * 10 ^ q := by grind
    have e4 : ((10 : Nat) : Rat) * 10 ^ big = 10 ^ (big + 1) := by
      rw [ten_zpow_succ]; grind
    refine ⟨h, e3, InI_convex hin hlo hhi (Or.inr ⟨by grind, by grind⟩)⟩

theorem optimal_near {lo hi X T : Rat} {incl : Bool} {c : Nat} (hT : 0 < T) (hlo : lo < X) (hhi : X < hi)
    (hX : 0 < X) (hc : InI lo hi incl ((c : Rat) * T))
    (hopt : ∀ y : Nat, InI lo hi incl ((y : Rat) * T) →
      ((c : Rat) * T - X).abs < ((y : Rat) * T - X).abs ∨
      (((c : Rat) * T - X).abs = ((y : Rat) * T - X).abs ∧ (y = c ∨ (c % 2 = 0 ∧ y % 2 = 1)))) :
    X - T < (c : Rat) * T ∧ (c : Rat) * T ≤ X + T := by
  constructor
  · apply Classical.byContradiction
    intro hn
    have hle : (c : Rat) * T ≤ X - T := Rat.not_lt.mp hn
    have hy : ((c + 1 : Nat) : Rat) * T = (c : Rat) * T + T := by rw [natCast_succ_rat]; grind
    have hin : InI lo hi incl (((c + 1 : Nat) : Rat) * T) :=
      InI_convex hc hlo hhi (Or.inl ⟨by grind, by grind⟩)
    have e1 : ((c : Rat) * T - X).abs = X - c * T := by rw [Rat.abs_of_nonpos (by grind)]; grind
    have e2 : (((c + 1 : Nat) : Rat) * T - X).abs = X - (c * T + T) := by
      rw [hy, Rat.abs_of_nonpos (by grind)]; grind
    rcases hopt (c + 1) hin with h | ⟨h, -⟩ <;> rw [e1, e2] at h <;> grind
  · apply Classical.byContradiction
    intro hn
    have hgt : X + T < (c : Rat) * T := Rat.not_le.mp hn
    have hc0 : c ≠ 0 := by
      rintro rfl
      have : ((0 : Nat) : Rat) * T = 0 := by rw [show ((0 : Nat) : Rat) = 0 from rfl]; grind
      grind
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    have hy : ((c' + 1 : Nat) : Rat) * T = (c' : Rat) * T + T := by rw [natCast_succ_rat]; grind
    have hin : InI lo hi incl ((c' : Rat) * T) := InI_convex hc hlo hhi (Or.inr ⟨by grind, by grind⟩)
    have e1 : (((c' + 1 : Nat) : Rat) * T - X).abs = c' * T + T - X := by
      rw [hy, Rat.abs_of_nonneg (by grind)]
    have e2 : ((c' : Rat) * T - X).abs = c' * T - X := by rw [Rat.abs_of_nonneg (by grind)]
    rcases hopt c' hin with h | ⟨h, -⟩ <;> rw [e1, e2] at h <;> grind

theorem d0_bounds (M : Nat) (e k : Int) :
    ((4 * M * (scale e k).1 / (scale e k).2 : Nat) : Rat) * 10 ^ k ≤ (M : Rat) * 2 ^ e ∧
      (M : Rat) * 2 ^ e < (((4 * M * (scale e k).1 / (scale e k).2 : Nat) : Rat) + 1) * 10 ^ k := by
  have ha := scale_fst_pos e k
  have hb := scale_snd_pos e k
  have hr := two_zpow_pos (e - 2)
  have hs := scale_rat e k
  have hX4 := four_mul_two_zpow M e
  generalize hd0 : 4 * M * (scale e k).1 / (scale e k).2 = d0
  have hdiv : d0 * (scale e k).2 ≤ 4 * M * (scale e k).1 := hd0 ▸ Nat.div_mul_le_self _ _
  have hlt : 4 * M * (scale e k).1 < (d0 + 1) * (scale e k).2 := by
    have := Nat.lt_div_mul_add (a := 4 * M * (scale e k).1) hb
    rw [hd0] at this
    rw [Nat.succ_mul d0 (scale e k).2]
    exact this
  refine ⟨?_, ?_⟩
  · rw [← hX4]
    exact (cross_le' ha hr hs (4 * M) d0).mp hdiv
  · rw [← hX4, ← natCast_succ_rat]
    exact (cross_lt ha hr hs (4 * M) (d0 + 1)).mp hlt

theorem candidate_isSome_of_fits {M : Nat} {e : Int} {lc incl : Bool} {k : Int}
    (hf : fits (roundingInterval M lc).1 (roundingInterval M lc).2.2 (scale e k).1 (scale e k).2 incl
          (4 * M * (scale e k).1 / (scale e k).2) = true ∨
        fits (roundingInterval M lc).1 (roundingInterval M lc).2.2 (scale e k).1 (scale e k).2 incl
          (4 * M * (scale e k).1 / (scale e k).2 + 1) = true) :
    (candidate M e lc incl k).isSome = true := by
  unfold candidate
  simp only
  split
  · split
    · rfl
    · split
      · rfl
      · split <;> rfl
  · rfl
  · rfl
  · rename_i h0 h1
    simp only [roundingInterval_mid] at h0 h1
    rcases hf with h | h
    · rw [h0] at h; cases h
    · rw [h1] at h; cases h

theorem candidate_isSome_of_InI {M : Nat} {e : Int} {lc incl : Bool} {k : Int} (hM : 0 < M) {y : Nat}
    (hy : InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2)) (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2))
      incl ((y : Rat) * 10 ^ k)) :
    (candidate M e lc incl k).isSome = true := by
  apply candidate_isSome_of_fits
  rw [fits_rat, fits_rat, natCast_succ_rat]
  obtain ⟨b0, b1⟩ := d0_bounds M e k
  generalize (4 * M * (scale e k).1 / (scale e k).2) = d0 at b0 b1 ⊢
  have hlo := roundingInterval_lo_lt M lc hM e
  have hhi := roundingInterval_hi_gt M lc e
  have hT := ten_zpow_pos k
  rcases Nat.lt_or_ge d0 y with h | h
  · right
    have h1 : ((d0 : Rat) + 1) ≤ y := by rw [← natCast_succ_rat]; exact Rat.natCast_le_natCast.mpr h
    have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hT)
    exact InI_convex hy hlo hhi (Or.inr ⟨Rat.le_of_lt b1, this⟩)
  · left
    have h1 : (y : Rat) ≤ d0 := Rat.natCast_le_natCast.mpr h
    have := Rat.mul_le_mul_of_nonneg_right h1 (Rat.le_of_lt hT)
    exact InI_convex hy hlo hhi (Or.inl ⟨this, b0⟩)

theorem searchDigits_least (cand : Nat → Bool) (L : Nat)
    (mono : ∀ p q, L ≤ p → p ≤ q → cand p = true → cand q = true) :
    ∀ (n lo hi : Nat), L ≤ lo → cand hi = true → lo ≤ hi → hi - lo < 2 ^ n →
      (∀ p, L ≤ p → p < lo → cand p = false) →
      ∀ p, L ≤ p → p < searchDigits cand n lo hi → cand p = false
  | 0, lo, hi, _, _, _, _, hbelow => by
    simp only [searchDigits]; exact hbelow
  | n + 1, lo, hi, hL, h, hle, hlt, hbelow => by
    simp only [searchDigits]
    split
    · split
      · rename_i _ hm
        exact searchDigits_least cand L mono n lo ((lo + hi) / 2) hL hm (by omega)
          (by rw [Nat.pow_succ] at hlt; omega) hbelow
      · rename_i _ hm
        apply searchDigits_least cand L mono n ((lo + hi) / 2 + 1) hi (by omega) h (by omega)
          (by rw [Nat.pow_succ] at hlt; omega)
        intro p hp1 hp2
        by_cases hpl : p < lo
        · exact hbelow p hp1 hpl
        · cases hc : cand p
          · rfl
          · exact absurd (mono p ((lo + hi) / 2) hp1 (by omega) hc) hm
    · exact hbelow

theorem searchDigits_bounds (cand : Nat → Bool) : ∀ (n lo hi : Nat), lo ≤ hi →
    lo ≤ searchDigits cand n lo hi ∧ searchDigits cand n lo hi ≤ hi
  | 0, lo, hi, hle => by simp only [searchDigits]; omega
  | n + 1, lo, hi, hle => by
    simp only [searchDigits]
    split
    · split
      · have := searchDigits_bounds cand n lo ((lo + hi) / 2) (by omega)
        omega
      · have := searchDigits_bounds cand n ((lo + hi) / 2 + 1) hi (by omega)
        omega
    · omega

theorem stripZeros_noTrailing : ∀ (n d : Nat) (x : Int), d ≠ 0 → d < 10 ^ n → (stripZeros n d x).1 % 10 ≠ 0
  | 0, d, x, hd, hlt => by simp at hlt; omega
  | n + 1, d, x, hd, hlt => by
    simp only [stripZeros]
    split
    · rename_i h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
      apply stripZeros_noTrailing n (d / 10) (x + 1) (by omega)
      rw [Nat.pow_succ] at hlt
      omega
    · rename_i h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, not_and] at h
      exact h hd

theorem two_pow_mod_five (j : Nat) : 2 ^ j % 5 ≠ 0 := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [Nat.pow_succ, Nat.mul_mod]
    have := Nat.mod_lt (2 ^ j) (show 0 < 5 by decide)
    generalize 2 ^ j % 5 = r at ih this
    rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl <;> decide

theorem no_tie_arith (M : Nat) (hM : 0 < M) (e k : Int)
    (htie : 2 * ((M : Rat) * 2 ^ e) = 19 * 10 ^ k) (hle : (10 : Rat) ^ k ≤ 2 ^ e) : False := by
  have h2 := powSplit_rat 2 (by decide) e
  have h10 := powSplit_rat 10 (by decide) k
  simp only [show ((2 : Nat) : Rat) = 2 from rfl, show ((10 : Nat) : Rat) = 10 from rfl] at h2 h10
  have p2 := powSplit_pos 2 (by decide) e
  have p10 := powSplit_pos 10 (by decide) k
  have eq : 2 * M * (powSplit 2 e).1 * (powSplit 10 k).2 = 19 * (powSplit 10 k).1 * (powSplit 2 e).2 := by
    apply Rat.natCast_inj.mp
    simp only [Rat.natCast_mul]
    rw [h2, h10]
    have h19 : ((19 : Nat) : Rat) = 19 := rfl
    have h2' : ((2 : Nat) : Rat) = 2 := rfl
    rw [h19, h2']
    calc 2 * (M : Rat) * (2 ^ e * ((powSplit 2 e).2 : Rat)) * ((powSplit 10 k).2 : Rat)
        = (2 * ((M : Rat) * 2 ^ e)) * ((powSplit 2 e).2 : Rat) * ((powSplit 10 k).2 : Rat) := by grind
      _ = 19 * 10 ^ k * ((powSplit 2 e).2 : Rat) * ((powSplit 10 k).2 : Rat) := by rw [htie]
      _ = 19 * (10 ^ k * ((powSplit 10 k).2 : Rat)) * ((powSplit 2 e).2 : Rat) := by grind
  have le : (powSplit 10 k).1 * (powSplit 2 e).2 ≤ (powSplit 2 e).1 * (powSplit 10 k).2 := by
    apply Rat.natCast_le_natCast.mp
    simp only [Rat.natCast_mul]
    rw [h2, h10]
    have hpos : (0 : Rat) ≤ ((powSplit 2 e).2 : Rat) * ((powSplit 10 k).2 : Rat) :=
      Rat.mul_nonneg Rat.natCast_nonneg Rat.natCast_nonneg
    have := Rat.mul_le_mul_of_nonneg_right hle hpos
    calc (10 : Rat) ^ k * ((powSplit 10 k).2 : Rat) * ((powSplit 2 e).2 : Rat)
        = 10 ^ k * (((powSplit 2 e).2 : Rat) * ((powSplit 10 k).2 : Rat)) := by grind
      _ ≤ 2 ^ e * (((powSplit 2 e).2 : Rat) * ((powSplit 10 k).2 : Rat)) := this
      _ = 2 ^ e * ((powSplit 2 e).2 : Rat) * ((powSplit 10 k).2 : Rat) := by grind
  unfold powSplit at eq le
  by_cases he : 0 ≤ e <;> by_cases hk : 0 ≤ k <;>
    simp only [he, hk, ↓reduceIte, Nat.mul_one, Nat.one_mul] at eq le
  · generalize e.toNat = a at eq le
    generalize k.toNat = b at eq le
    have hb2 : 2 ^ b ≤ 10 ^ b := Nat.pow_le_pow_left (by decide) b
    have hba : b ≤ a := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (Nat.le_trans hb2 le)
    have h10 : 10 ^ b = 2 ^ b * 5 ^ b := by rw [show (10 : Nat) = 2 * 5 by rfl, Nat.mul_pow]
    have ha : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by rw [← Nat.pow_add]; congr 1; omega
    rw [h10, ha] at eq
    have eq' : 2 ^ b * (2 * M * 2 ^ (a - b)) = 2 ^ b * (19 * 5 ^ b) := by
      calc 2 ^ b * (2 * M * 2 ^ (a - b)) = 2 * M * (2 ^ b * 2 ^ (a - b)) := by ac_rfl
        _ = 19 * (2 ^ b * 5 ^ b) := eq
        _ = 2 ^ b * (19 * 5 ^ b) := by ac_rfl
    have eq'' := Nat.eq_of_mul_eq_mul_left (Nat.pow_pos (by decide)) eq'
    have h5 : 5 ^ b % 2 = 1 := by rw [Nat.pow_mod]; simp
    have : (2 * M * 2 ^ (a - b)) % 2 = 0 := by rw [Nat.mul_assoc]; exact Nat.mul_mod_right 2 _
    rw [eq''] at this
    omega
  · generalize e.toNat = a at eq le
    generalize hb' : (-k).toNat = b at eq le
    have hb : 1 ≤ b := by omega
    have h1 : 10 ≤ 10 ^ b := by
      calc 10 = 10 ^ 1 := rfl
        _ ≤ 10 ^ b := Nat.pow_le_pow_right (by decide) hb
    have h2 : 1 ≤ M * 2 ^ a := Nat.mul_pos hM (Nat.pow_pos (by decide))
    have : 2 * 1 * 10 ≤ 2 * (M * 2 ^ a) * 10 ^ b :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 h2) h1
    rw [← Nat.mul_assoc 2 M] at this
    omega
  · generalize ha' : (-e).toNat = a at eq le
    generalize k.toNat = b at eq le
    have ha : 1 ≤ a := by omega
    have h1 : 2 ≤ 2 ^ a := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by decide) ha
    have h2 : 1 ≤ 10 ^ b := Nat.pow_pos (by decide)
    have : 1 * 2 ≤ 10 ^ b * 2 ^ a := Nat.mul_le_mul h2 h1
    omega
  · generalize (-e).toNat = a at eq le
    generalize hb' : (-k).toNat = b at eq le
    have hb : 1 ≤ b := by omega
    have h10 : 10 ^ b = 5 * (2 * 10 ^ (b - 1)) := by
      rw [show b = (b - 1) + 1 by omega, Nat.pow_succ]
      simp only [Nat.add_sub_cancel]
      omega
    rw [h10] at eq
    have hl : (2 * M * (5 * (2 * 10 ^ (b - 1)))) % 5 = 0 := by
      rw [show 2 * M * (5 * (2 * 10 ^ (b - 1))) = 5 * (2 * M * (2 * 10 ^ (b - 1))) by ac_rfl]
      exact Nat.mul_mod_right 5 _
    rw [eq] at hl
    have := two_pow_mod_five a
    have h19 : (19 * 2 ^ a) % 5 = (4 * (2 ^ a % 5)) % 5 := by
      rw [Nat.mul_mod]
    rw [h19] at hl
    have hlt := Nat.mod_lt (2 ^ a) (show 0 < 5 by decide)
    generalize 2 ^ a % 5 = r at hl this hlt
    rcases (by omega : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4) with rfl | rfl | rfl | rfl <;> simp at hl

theorem no_tie {M : Nat} {e : Int} {lc incl : Bool} {k : Int} (hM : 0 < M)
    (h9 : InI (((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2)) (((roundingInterval M lc).2.2 : Rat) * 2 ^ (e - 2))
      incl (((9 : Nat) : Rat) * 10 ^ k))
    (htie : 2 * ((M : Rat) * 2 ^ e) = 19 * 10 ^ k) : False := by
  apply no_tie_arith M hM e k htie
  have hlow : (roundingInterval M lc).1 + 2 ≥ 4 * M := by
    unfold roundingInterval; split <;> omega
  have hlow' : ((roundingInterval M lc).1 : Rat) + 2 ≥ 4 * (M : Rat) := by
    have := Rat.natCast_le_natCast.mpr hlow
    simp only [Rat.natCast_add, Rat.natCast_mul] at this
    exact this
  have hr := two_zpow_pos (e - 2)
  have hm := Rat.mul_le_mul_of_nonneg_right hlow' (Rat.le_of_lt hr)
  have h2e := two_zpow_sub_two e
  have h9' : ((9 : Nat) : Rat) = 9 := rfl
  unfold InI at h9
  rw [h9'] at h9
  have hlo9 : ((roundingInterval M lc).1 : Rat) * 2 ^ (e - 2) ≤ 9 * 10 ^ k := by
    rcases h9.1 with h | ⟨-, h⟩
    · exact Rat.le_of_lt h
    · rw [h]; exact Rat.le_refl
  rw [h2e] at htie ⊢
  grind

theorem nat_lt_of_mul_lt {a b : Nat} {T : Rat} (hT : 0 < T) (h : (a : Rat) * T < (b : Rat) * T) : a < b :=
  Rat.natCast_lt_natCast.mp ((Rat.mul_lt_mul_right hT).mp h)

theorem floatValue_eq {x : Float} {neg : Bool} {M : Nat} {e : Int} (hd : decompose x = (neg, M, e)) :
    floatValue x = if neg then -((M : Rat) * 2 ^ e) else (M : Rat) * 2 ^ e := by
  unfold floatValue
  unfold decompose at hd
  simp only at hd
  split at hd
  · rename_i h0
    simp only [Prod.mk.injEq] at hd
    obtain ⟨hn, hM, he⟩ := hd
    subst hM he
    simp only [h0, ↓reduceIte]
    rw [← hn]
    by_cases hs : x.toBits.toNat ≥ 2 ^ 63 <;> simp only [hs, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]
  · rename_i h0
    simp only [Prod.mk.injEq] at hd
    obtain ⟨hn, hM, he⟩ := hd
    subst hM he
    simp only [h0, ↓reduceIte]
    rw [← hn]
    by_cases hs : x.toBits.toNat ≥ 2 ^ 63 <;> simp only [hs, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true]

theorem roundsTo_rat (M : Nat) (e : Int) (m : Nat) (q : Int) :
    roundsTo M e m q = true ↔
      InI (((roundingInterval M (decide (M = 2 ^ 52) && decide (e > -1074))).1 : Rat) * 2 ^ (e - 2))
        (((roundingInterval M (decide (M = 2 ^ 52) && decide (e > -1074))).2.2 : Rat) * 2 ^ (e - 2))
        (M % 2 == 0) ((m : Rat) * 10 ^ q) := by
  unfold roundsTo
  exact fits_rat _ _ e q _ m

end FloatText

end ExactJSON
