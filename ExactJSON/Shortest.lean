module

public import ExactJSON.Float

/-! # The shortest decimal of a float reads back as it

`FloatText.shortest x`, for a finite nonzero `x = m × 2^e`, gives a decimal `d × 10^k` inside the
interval of reals that round to `x`: the half-ulp interval, its ends included when `m` is even
(`fits`, at the scale `scale e k`). These lemmas show it always gives one: the decimal exponent
it starts from is exact, 17 digits always fit, and the search and the trailing zeros it removes
keep the decimal inside the interval.
-/

public section

namespace ExactJSON

namespace FloatText

/-! ## Powers of ten and two as fractions -/

theorem powSplit_pos (a : Nat) (ha : 0 < a) (k : Int) : 0 < (powSplit a k).1 ∧ 0 < (powSplit a k).2 := by
  unfold powSplit
  split
  · exact ⟨Nat.pow_pos ha, Nat.one_pos⟩
  · exact ⟨Nat.one_pos, Nat.pow_pos ha⟩

/-- `a ^ (k₁ + k₂) = a ^ k₁ × a ^ k₂`, as fractions. -/
theorem powSplit_add (a : Nat) (k₁ k₂ : Int) :
    (powSplit a (k₁ + k₂)).1 * ((powSplit a k₁).2 * (powSplit a k₂).2) =
      (powSplit a k₁).1 * (powSplit a k₂).1 * (powSplit a (k₁ + k₂)).2 := by
  unfold powSplit
  by_cases h1 : 0 ≤ k₁ <;> by_cases h2 : 0 ≤ k₂ <;> by_cases h3 : 0 ≤ k₁ + k₂ <;>
    simp only [h1, h2, h3, ite_true, ite_false, Nat.mul_one, Nat.one_mul]
  all_goals first
    | omega
    | (rw [← Nat.pow_add]; congr 1; omega)
    | (rw [← Nat.pow_add, ← Nat.pow_add]; congr 1; omega)
    | (rw [Nat.mul_comm, ← Nat.pow_add]; congr 1; omega)

/-- `a ^ k ≤ a ^ k'` for `k ≤ k'`, as fractions. -/
theorem powSplit_mono (a : Nat) (ha : 0 < a) {k k' : Int} (hk : k ≤ k') :
    (powSplit a k).1 * (powSplit a k').2 ≤ (powSplit a k').1 * (powSplit a k).2 := by
  have h := powSplit_add a k (k' - k)
  rw [show k + (k' - k) = k' by omega] at h
  have hp := powSplit_pos a ha (k' - k)
  have hk0 : 0 ≤ k' - k := by omega
  have hs : powSplit a (k' - k) = (a ^ (k' - k).toNat, 1) := by
    unfold powSplit
    simp only [hk0, ↓reduceIte]
  rw [hs] at h
  simp only [Nat.mul_one] at h
  -- `a ^ k' × d = a ^ k × a ^ j × d'`, and `a ^ j ≥ 1`
  have hj : 1 ≤ a ^ (k' - k).toNat := Nat.pow_pos ha
  calc (powSplit a k).1 * (powSplit a k').2
      ≤ (powSplit a k).1 * a ^ (k' - k).toNat * (powSplit a k').2 := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hj)
    _ = (powSplit a k').1 * (powSplit a k).2 := by rw [← h]

/-- `tenPowLe k m e` says `10 ^ k ≤ m × 2 ^ e`; it holds for smaller `k` too. -/
theorem tenPowLe_mono {k k' : Int} {m : Nat} {e : Int} (hk : k ≤ k') (h : tenPowLe k' m e = true) :
    tenPowLe k m e = true := by
  unfold tenPowLe at h ⊢
  simp only [decide_eq_true_eq] at h ⊢
  have hm := powSplit_mono 10 (by decide) hk
  have hpos := (powSplit_pos 10 (by decide) k').2
  -- multiply the goal by the denominator of `10 ^ k'`
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc (powSplit 10 k).1 * (powSplit 2 e).2 * (powSplit 10 k').2
      = (powSplit 10 k).1 * (powSplit 10 k').2 * (powSplit 2 e).2 := by ac_rfl
    _ ≤ (powSplit 10 k').1 * (powSplit 10 k).2 * (powSplit 2 e).2 := Nat.mul_le_mul_right _ hm
    _ = (powSplit 10 k').1 * (powSplit 2 e).2 * (powSplit 10 k).2 := by ac_rfl
    _ ≤ m * (powSplit 2 e).1 * (powSplit 10 k').2 * (powSplit 10 k).2 := Nat.mul_le_mul_right _ h
    _ = m * (powSplit 2 e).1 * (powSplit 10 k).2 * (powSplit 10 k').2 := by ac_rfl

/-! ## The decimal exponent is exact -/

theorem lowerExponent_spec (m : Nat) (e : Int) : ∀ (n : Nat) (k : Int), tenPowLe (k - n) m e = true →
    tenPowLe (lowerExponent m e n k) m e = true ∧ k - n ≤ lowerExponent m e n k ∧
      lowerExponent m e n k ≤ k ∧ (lowerExponent m e n k < k → tenPowLe (lowerExponent m e n k + 1) m e = false)
  | 0, k, h => by simp only [lowerExponent]; exact ⟨by simpa using h, by omega, by omega, by omega⟩
  | n + 1, k, h => by
    simp only [lowerExponent]
    split
    · rename_i hk
      exact ⟨hk, by omega, by omega, by omega⟩
    · rename_i hk
      have ih := lowerExponent_spec m e n (k - 1) (by rw [show k - 1 - n = k - ↑(n + 1) by omega]; exact h)
      obtain ⟨h1, h2, h3, h4⟩ := ih
      refine ⟨h1, by omega, by omega, fun _ => ?_⟩
      by_cases hlt : lowerExponent m e n (k - 1) < k - 1
      · exact h4 hlt
      · rw [show lowerExponent m e n (k - 1) + 1 = k by omega]
        simpa using hk

theorem raiseExponent_spec (m : Nat) (e : Int) : ∀ (n : Nat) (k : Int), tenPowLe k m e = true →
    tenPowLe (k + n + 1) m e = false →
    tenPowLe (raiseExponent m e n k) m e = true ∧ tenPowLe (raiseExponent m e n k + 1) m e = false
  | 0, k, h1, h2 => by simp only [raiseExponent]; exact ⟨h1, by simpa using h2⟩
  | n + 1, k, h1, h2 => by
    simp only [raiseExponent]
    split
    · rename_i hk
      exact raiseExponent_spec m e n (k + 1) hk (by rw [show k + 1 + n + 1 = k + ↑(n + 1) + 1 by omega]; exact h2)
    · rename_i hk
      exact ⟨h1, by simpa using hk⟩

/-- The estimate of `⌊log₁₀ 2^n⌋` is off by less than four either way, for every binary exponent
of a finite float: `10 ^ (k - 4) ≤ 2 ^ n` and `2 ^ (n + 1) ≤ 10 ^ (k + 5)`. -/
def estimateBrackets (n : Int) : Bool :=
  let k := (n * 78913) / 262144
  let (tn, td) := powSplit 10 (k - 4)
  let (bn, bd) := powSplit 2 n
  let (tn', td') := powSplit 10 (k + 5)
  let (bn', bd') := powSplit 2 (n + 1)
  tn * bd ≤ bn * td && bn' * td' ≤ tn' * bd'

/-- `estimateBrackets` for the `count` exponents from `-1074`. -/
def allBrackets : Nat → Bool
  | 0 => true
  | i + 1 => estimateBrackets ((i : Int) - 1074) && allBrackets i

set_option maxRecDepth 100000 in
theorem allBrackets_true : allBrackets 2098 = true := by decide +kernel

theorem estimateBrackets_of (n : Int) (h1 : -1074 ≤ n) (h2 : n ≤ 1023) : estimateBrackets n = true := by
  have key : ∀ i : Nat, i < 2098 → estimateBrackets ((i : Int) - 1074) = true := by
    intro i hi
    have : ∀ j : Nat, allBrackets j = true → i < j → estimateBrackets ((i : Int) - 1074) = true := by
      intro j
      induction j with
      | zero => intro _ h; omega
      | succ j ih =>
        intro h hij
        simp only [allBrackets, Bool.and_eq_true] at h
        by_cases hj : i = j
        · subst hj
          exact h.1
        · exact ih h.2 (by omega)
    exact this 2098 allBrackets_true hi
  have := key (n + 1074).toNat (by omega)
  rwa [show (((n + 1074).toNat : Nat) : Int) - 1074 = n by omega] at this

theorem powSplit_nat (a : Nat) (L : Nat) : powSplit a (L : Int) = (a ^ L, 1) := by
  simp [powSplit]

/-- `2 ^ (L + e) = 2 ^ L × 2 ^ e`, as a fraction of `2 ^ e`'s. -/
theorem powSplit_two_add (L : Nat) (e : Int) :
    (powSplit 2 (L + e)).1 * (powSplit 2 e).2 = 2 ^ L * (powSplit 2 e).1 * (powSplit 2 (L + e)).2 := by
  have h := powSplit_add 2 L e
  rw [powSplit_nat] at h
  simpa using h

theorem tenPowLe_of_le (k : Int) (m L : Nat) (e : Int) (hL : 2 ^ L ≤ m)
    (h : (powSplit 10 k).1 * (powSplit 2 (L + e)).2 ≤ (powSplit 2 (L + e)).1 * (powSplit 10 k).2) :
    tenPowLe k m e = true := by
  unfold tenPowLe
  simp only [decide_eq_true_eq]
  have hd := (powSplit_pos 2 (by decide) (L + e)).2
  have hadd := powSplit_two_add L e
  refine Nat.le_of_mul_le_mul_right ?_ hd
  calc (powSplit 10 k).1 * (powSplit 2 e).2 * (powSplit 2 (L + e)).2
      = (powSplit 10 k).1 * (powSplit 2 (L + e)).2 * (powSplit 2 e).2 := by ac_rfl
    _ ≤ (powSplit 2 (L + e)).1 * (powSplit 10 k).2 * (powSplit 2 e).2 := Nat.mul_le_mul_right _ h
    _ = (powSplit 2 (L + e)).1 * (powSplit 2 e).2 * (powSplit 10 k).2 := by ac_rfl
    _ = 2 ^ L * (powSplit 2 e).1 * (powSplit 2 (L + e)).2 * (powSplit 10 k).2 := by rw [hadd]
    _ ≤ m * (powSplit 2 e).1 * (powSplit 2 (L + e)).2 * (powSplit 10 k).2 := by
      apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_right _ hL
    _ = m * (powSplit 2 e).1 * (powSplit 10 k).2 * (powSplit 2 (L + e)).2 := by ac_rfl

theorem tenPowLe_false_of_lt (k : Int) (m L : Nat) (e : Int) (hL : m < 2 ^ L)
    (h : (powSplit 2 (L + e)).1 * (powSplit 10 k).2 ≤ (powSplit 10 k).1 * (powSplit 2 (L + e)).2) :
    tenPowLe k m e = false := by
  unfold tenPowLe
  simp only [decide_eq_false_iff_not, Nat.not_le]
  have hd := (powSplit_pos 2 (by decide) (L + e)).2
  have hb := (powSplit_pos 2 (by decide) e).1
  have ht := (powSplit_pos 10 (by decide) k).2
  have hadd := powSplit_two_add L e
  refine Nat.lt_of_mul_lt_mul_right (a := (powSplit 2 (L + e)).2) ?_
  calc m * (powSplit 2 e).1 * (powSplit 10 k).2 * (powSplit 2 (L + e)).2
      < 2 ^ L * (powSplit 2 e).1 * (powSplit 10 k).2 * (powSplit 2 (L + e)).2 := by
        apply Nat.mul_lt_mul_of_pos_right _ hd
        apply Nat.mul_lt_mul_of_pos_right _ ht
        exact Nat.mul_lt_mul_of_pos_right hL hb
    _ = (powSplit 2 (L + e)).1 * (powSplit 2 e).2 * (powSplit 10 k).2 := by rw [hadd]; ac_rfl
    _ = (powSplit 2 (L + e)).1 * (powSplit 10 k).2 * (powSplit 2 e).2 := by ac_rfl
    _ ≤ (powSplit 10 k).1 * (powSplit 2 (L + e)).2 * (powSplit 2 e).2 := Nat.mul_le_mul_right _ h
    _ = (powSplit 10 k).1 * (powSplit 2 e).2 * (powSplit 2 (L + e)).2 := by ac_rfl

/-- `decimalExponent m e` is `⌊log₁₀ (m × 2 ^ e)⌋`: `10 ^ E ≤ m × 2 ^ e < 10 ^ (E + 1)`. -/
theorem decimalExponent_spec (m : Nat) (e : Int) (hm : 0 < m) (h1 : -1074 ≤ (Nat.log2 m : Int) + e)
    (h2 : (Nat.log2 m : Int) + e ≤ 1023) :
    tenPowLe (decimalExponent m e) m e = true ∧ tenPowLe (decimalExponent m e + 1) m e = false := by
  have hb := estimateBrackets_of _ h1 h2
  unfold estimateBrackets at hb
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨b1, b2⟩ := hb
  have lo : tenPowLe ((((Nat.log2 m : Int) + e) * 78913) / 262144 - 4) m e = true :=
    tenPowLe_of_le _ m (Nat.log2 m) e (Nat.log2_self_le (by omega)) b1
  have hi : tenPowLe ((((Nat.log2 m : Int) + e) * 78913) / 262144 + 5) m e = false := by
    apply tenPowLe_false_of_lt _ m (Nat.log2 m + 1) e (Nat.lt_log2_self)
    rw [show ((Nat.log2 m + 1 : Nat) : Int) + e = (Nat.log2 m : Int) + e + 1 by omega]
    exact b2
  unfold decimalExponent
  simp only
  generalize hk0 : (((Nat.log2 m : Int) + e) * 78913) / 262144 = k0 at lo hi
  obtain ⟨r1, r2, r3, r4⟩ := lowerExponent_spec m e 4 k0 (by simpa using lo)
  apply raiseExponent_spec m e 4 _ r1
  by_cases hr : lowerExponent m e 4 k0 < k0
  · have := r4 hr
    cases h : tenPowLe (lowerExponent m e 4 k0 + ↑(4 : Nat) + 1) m e
    · rfl
    · have := tenPowLe_mono (k := lowerExponent m e 4 k0 + 1) (by omega) h
      simp_all
  · rw [show lowerExponent m e 4 k0 + ↑(4 : Nat) + 1 = k0 + 5 by omega]
    exact hi

/-! ## A candidate fits the rounding interval, and one exists when the interval is wide -/

theorem candidate_fits {m : Nat} {e : Int} {lc incl : Bool} {k : Int} {d : Nat}
    (h : candidate m e lc incl k = some d) :
    fits (roundingInterval m lc).1 (roundingInterval m lc).2.2 (scale e k).1 (scale e k).2 incl d = true := by
  unfold candidate at h
  simp only at h
  split at h
  · rename_i h0 h1
    split at h
    · cases h; exact h0
    · split at h
      · cases h; exact h1
      · split at h <;> (cases h; first | exact h0 | exact h1)
  · rename_i h0 _
    cases h; exact h0
  · rename_i _ h1
    cases h; exact h1
  · cases h

/-- A candidate exists when, in units of `10 ^ k`, the interval reaches more than half a unit on
each side of `x`, or more than a unit above it. -/
theorem candidate_isSome {m : Nat} {e : Int} {lc incl : Bool} {k : Int} (hm : 0 < m)
    (hwide : let (low, x, high) := roundingInterval m lc
      let (a, b) := scale e k
      (b < 2 * ((x - low) * a) ∧ b < 2 * ((high - x) * a)) ∨ b < (high - x) * a) :
    (candidate m e lc incl k).isSome = true := by
  have hb : 0 < (scale e k).2 := by
    unfold scale
    exact Nat.mul_pos (powSplit_pos 2 (by decide) _).2 (powSplit_pos 10 (by decide) _).1
  have ha : 0 < (scale e k).1 := by
    unfold scale
    exact Nat.mul_pos (powSplit_pos 2 (by decide) _).1 (powSplit_pos 10 (by decide) _).2
  generalize hs : scale e k = ab at hb ha hwide
  obtain ⟨a, b⟩ := ab
  generalize hr : roundingInterval m lc = lxh at hwide
  obtain ⟨low, x, high⟩ := lxh
  have hlx : low < x ∧ x < high ∧ x = 4 * m := by
    unfold roundingInterval at hr
    simp only [Prod.mk.injEq] at hr
    obtain ⟨h1, h2, h3⟩ := hr
    split at h1 <;> omega
  simp only at hwide ha hb
  -- the two candidates, as multiples of `b`
  have hdiv := Nat.div_mul_le_self (x * a) b
  have hlt := Nat.lt_div_mul_add (a := x * a) hb
  have fits_of : ∀ d, low * a < d * b → d * b < high * a → fits low high a b incl d = true := by
    intro d h1 h2
    simp [fits, h1, h2]
  unfold candidate
  simp only [hs, hr]
  generalize hd0 : x * a / b = d0 at hdiv hlt
  have hla : low * a < x * a := Nat.mul_lt_mul_of_pos_right hlx.1 ha
  have hxa : x * a < high * a := Nat.mul_lt_mul_of_pos_right hlx.2.1 ha
  have hsub1 : (x - low) * a = x * a - low * a := Nat.sub_mul _ _ _
  have hsub2 : (high - x) * a = high * a - x * a := Nat.sub_mul _ _ _
  rw [hsub1, hsub2] at hwide
  have hd1b : (d0 + 1) * b = d0 * b + b := Nat.succ_mul _ _
  -- one of `d0` and `d0 + 1` fits
  have : fits low high a b incl d0 = true ∨ fits low high a b incl (d0 + 1) = true := by
    rcases hwide with ⟨w1, w2⟩ | w
    · by_cases hr2 : 2 * (x * a - d0 * b) ≤ b
      · left
        exact fits_of d0 (by omega) (by omega)
      · right
        exact fits_of (d0 + 1) (by omega) (by omega)
    · by_cases heq : d0 * b = x * a
      · left
        exact fits_of d0 (by omega) (by omega)
      · right
        exact fits_of (d0 + 1) (by omega) (by omega)
  rcases this with h0 | h1
  · cases fits low high a b incl (d0 + 1) <;> simp only [h0] <;> (repeat' split) <;> simp
  · cases fits low high a b incl d0 <;> simp only [h1] <;> (repeat' split) <;> simp

/-! ## Seventeen digits always fit -/

/-- At `10 ^ (E - 16)`, for `10 ^ E ≤ M × 2 ^ e`, a unit is smaller than `c` quarter-units of
`2 ^ e` whenever `4 M < c × 10 ^ 16`. -/
theorem scale_wide (M : Nat) (e E : Int) (hE : tenPowLe E M e = true) (c : Nat) (hc : M * 4 < c * 10 ^ 16) :
    (scale e (E - 16)).2 < c * (scale e (E - 16)).1 := by
  unfold tenPowLe at hE
  simp only [decide_eq_true_eq] at hE
  -- the fractions: `2 ^ e = 4 × 2 ^ (e - 2)` and `10 ^ E = 10 ^ 16 × 10 ^ (E - 16)`
  have h2 := powSplit_add 2 2 (e - 2)
  rw [show (2 : Int) + (e - 2) = e by omega, show ((2 : Int)) = ((2 : Nat) : Int) by rfl, powSplit_nat] at h2
  have h10 := powSplit_add 10 16 (E - 16)
  rw [show (16 : Int) + (E - 16) = E by omega, show ((16 : Int)) = ((16 : Nat) : Int) by rfl, powSplit_nat] at h10
  simp only [Nat.one_mul] at h2 h10
  have p2 := powSplit_pos 2 (by decide) (e - 2)
  have p10 := powSplit_pos 10 (by decide) (E - 16)
  have hBn := (powSplit_pos 2 (by decide) e).1
  have hBd := (powSplit_pos 2 (by decide) e).2
  have hTd := (powSplit_pos 10 (by decide) E).2
  unfold scale
  simp only
  generalize powSplit 2 (e - 2) = q2 at h2 p2 ⊢
  generalize powSplit 10 (E - 16) = q10 at h10 p10 ⊢
  obtain ⟨a2, b2⟩ := q2
  obtain ⟨b10, a10⟩ := q10
  simp only at h2 h10 p2 p10 ⊢
  refine Nat.lt_of_mul_lt_mul_right (a := (powSplit 2 e).2 * (powSplit 10 E).2 * 10 ^ 16) ?_
  calc b2 * b10 * ((powSplit 2 e).2 * (powSplit 10 E).2 * 10 ^ 16)
      = b2 * (powSplit 2 e).2 * (10 ^ 16 * b10 * (powSplit 10 E).2) := by ac_rfl
    _ = b2 * (powSplit 2 e).2 * ((powSplit 10 E).1 * a10) := by rw [h10]
    _ = b2 * a10 * ((powSplit 10 E).1 * (powSplit 2 e).2) := by ac_rfl
    _ ≤ b2 * a10 * (M * (powSplit 2 e).1 * (powSplit 10 E).2) := Nat.mul_le_mul_left _ hE
    _ = a10 * M * (powSplit 10 E).2 * ((powSplit 2 e).1 * b2) := by ac_rfl
    _ = a10 * M * (powSplit 10 E).2 * (2 ^ 2 * a2 * (powSplit 2 e).2) := by rw [h2]
    _ = (M * 4) * (a10 * a2 * (powSplit 2 e).2 * (powSplit 10 E).2) := by
      rw [show (2 : Nat) ^ 2 = 4 by rfl]; ac_rfl
    _ < (c * 10 ^ 16) * (a10 * a2 * (powSplit 2 e).2 * (powSplit 10 E).2) :=
      Nat.mul_lt_mul_of_pos_right hc (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos p10.2 p2.1) hBd) hTd)
    _ = c * (a2 * a10) * ((powSplit 2 e).2 * (powSplit 10 E).2 * 10 ^ 16) := by ac_rfl

/-! ## Moving trailing zeros into the exponent keeps a decimal in the interval -/

theorem fits_scale (low high : Nat) (e k : Int) (incl : Bool) (d j : Nat) :
    fits low high (scale e k).1 (scale e k).2 incl (d * 10 ^ j) =
      fits low high (scale e (k + j)).1 (scale e (k + j)).2 incl d := by
  have h10 := powSplit_add 10 k j
  rw [powSplit_nat] at h10
  simp only [Nat.mul_one] at h10
  have pa := (powSplit_pos 10 (by decide) k).2
  have pa' := (powSplit_pos 10 (by decide) (k + j)).2
  unfold scale fits
  simp only
  generalize powSplit 2 (e - 2) = q2
  obtain ⟨a2, b2⟩ := q2
  generalize powSplit 10 k = q at h10 pa
  generalize powSplit 10 (k + j) = q' at h10 pa'
  obtain ⟨b10, a10⟩ := q
  obtain ⟨b10', a10'⟩ := q'
  simp only at h10 pa pa' ⊢
  -- every comparison scales by `a10` on one side and `a10'` on the other
  have key : ∀ y : Nat, (y * (a2 * a10)) * a10' = (y * (a2 * a10')) * a10 := fun y => by ac_rfl
  have keyv : (d * 10 ^ j * (b2 * b10)) * a10' = (d * (b2 * b10')) * a10 := by
    calc (d * 10 ^ j * (b2 * b10)) * a10' = d * b2 * (b10 * 10 ^ j * a10') := by ac_rfl
      _ = d * b2 * (b10' * a10) := by rw [← h10]
      _ = (d * (b2 * b10')) * a10 := by ac_rfl
  have lt_iff : ∀ y : Nat, y * (a2 * a10) < d * 10 ^ j * (b2 * b10) ↔ y * (a2 * a10') < d * (b2 * b10') := by
    intro y
    rw [← Nat.mul_lt_mul_right pa', key, keyv, Nat.mul_lt_mul_right pa]
  have gt_iff : ∀ y : Nat, d * 10 ^ j * (b2 * b10) < y * (a2 * a10) ↔ d * (b2 * b10') < y * (a2 * a10') := by
    intro y
    rw [← Nat.mul_lt_mul_right pa', key, keyv, Nat.mul_lt_mul_right pa]
  have eq_iff : ∀ y : Nat, y * (a2 * a10) = d * 10 ^ j * (b2 * b10) ↔ y * (a2 * a10') = d * (b2 * b10') := by
    intro y
    constructor
    · intro h
      have := congrArg (· * a10') h
      rw [key, keyv] at this
      exact Nat.eq_of_mul_eq_mul_right pa this
    · intro h
      have := congrArg (· * a10) h
      rw [← key, ← keyv] at this
      exact Nat.eq_of_mul_eq_mul_right pa' this
  have eq_iff' : ∀ y : Nat, d * 10 ^ j * (b2 * b10) = y * (a2 * a10) ↔ d * (b2 * b10') = y * (a2 * a10') := by
    intro y
    rw [eq_comm, eq_iff y, eq_comm]
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, lt_iff, gt_iff, eq_iff, eq_iff']

theorem stripZeros_spec : ∀ (n d : Nat) (x : Int),
    ∃ j : Nat, d = (stripZeros n d x).1 * 10 ^ j ∧ (stripZeros n d x).2 = x + j
  | 0, d, x => ⟨0, by simp [stripZeros], by simp [stripZeros]⟩
  | n + 1, d, x => by
    simp only [stripZeros]
    split
    · rename_i h
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
      obtain ⟨j, h1, h2⟩ := stripZeros_spec n (d / 10) (x + 1)
      refine ⟨j + 1, ?_, by rw [h2]; omega⟩
      calc d = d / 10 * 10 := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.2)).symm
        _ = (stripZeros n (d / 10) (x + 1)).1 * 10 ^ j * 10 := by rw [← h1]
        _ = (stripZeros n (d / 10) (x + 1)).1 * 10 ^ (j + 1) := by rw [Nat.pow_succ, Nat.mul_assoc]
    · exact ⟨0, by simp, by simp⟩

theorem searchDigits_spec (cand : Nat → Bool) : ∀ (n lo hi : Nat), cand hi = true → lo ≤ hi →
    hi - lo < 2 ^ n → cand (searchDigits cand n lo hi) = true
  | 0, lo, hi, h, hle, hlt => by
    simp only [searchDigits]
    have : lo = hi := by simp at hlt; omega
    rw [this]; exact h
  | n + 1, lo, hi, h, hle, hlt => by
    simp only [searchDigits]
    split
    · split
      · rename_i _ hm
        exact searchDigits_spec cand n lo ((lo + hi) / 2) hm (by omega) (by rw [Nat.pow_succ] at hlt; omega)
      · exact searchDigits_spec cand n ((lo + hi) / 2 + 1) hi h (by omega) (by rw [Nat.pow_succ] at hlt; omega)
    · have : lo = hi := by omega
      rw [this]; exact h

/-! ## The shortest decimal of a finite float is in its interval -/

theorem decompose_spec (x : Float) (hx : finiteFloat x = true) (neg : Bool) (M : Nat) (e : Int)
    (hd : decompose x = (neg, M, e)) :
    M < 2 ^ 53 ∧ (M ≠ 0 → -1074 ≤ (Nat.log2 M : Int) + e ∧ (Nat.log2 M : Int) + e ≤ 1023) := by
  unfold finiteFloat at hx
  unfold decompose at hd
  simp only at hd
  simp only [bne_iff_ne, ne_eq] at hx
  have hfr : x.toBits.toNat % 2 ^ 52 < 2 ^ 52 := Nat.mod_lt _ (by decide)
  have hbi : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 < 2 ^ 11 := Nat.mod_lt _ (by decide)
  split at hd
  · rename_i h0
    simp only [Prod.mk.injEq] at hd
    obtain ⟨-, rfl, rfl⟩ := hd
    refine ⟨by omega, fun hM => ?_⟩
    have := (Nat.log2_lt hM).mpr (show x.toBits.toNat % 2 ^ 52 < 2 ^ 52 from hfr)
    omega
  · rename_i h0
    simp only [Prod.mk.injEq] at hd
    obtain ⟨-, rfl, rfl⟩ := hd
    have hM : x.toBits.toNat % 2 ^ 52 + 2 ^ 52 ≠ 0 := by omega
    have l1 := (Nat.log2_lt hM).mpr (show x.toBits.toNat % 2 ^ 52 + 2 ^ 52 < 2 ^ 53 by omega)
    have l2 := (Nat.le_log2 hM).mpr (show 2 ^ 52 ≤ x.toBits.toNat % 2 ^ 52 + 2 ^ 52 by omega)
    refine ⟨by omega, fun _ => ?_⟩
    have : x.toBits.toNat / 2 ^ 52 % 2 ^ 11 ≤ 2046 := by omega
    omega

/-- The shortest decimal of a finite nonzero float lies in its rounding interval. -/
theorem shortest_spec (x : Float) (hx : finiteFloat x = true) (neg : Bool) (M : Nat) (e : Int)
    (hd : decompose x = (neg, M, e)) (hM : M ≠ 0) :
    ∃ dd : Decimal, shortest x = some dd ∧ dd.negative = neg ∧
      fits (roundingInterval M (decide (M = 2 ^ 52) && decide (e > -1074))).1
        (roundingInterval M (decide (M = 2 ^ 52) && decide (e > -1074))).2.2
        (scale e dd.exponent).1 (scale e dd.exponent).2 (M % 2 == 0) dd.digits = true := by
  obtain ⟨hM53, hrange⟩ := decompose_spec x hx neg M e hd
  obtain ⟨hr1, hr2⟩ := hrange hM
  obtain ⟨hE, -⟩ := decimalExponent_spec M e (Nat.pos_of_ne_zero hM) hr1 hr2
  generalize hlc : (decide (M = 2 ^ 52) && decide (e > -1074)) = lc
  generalize hincl : (M % 2 == 0) = incl
  generalize hbig : decimalExponent M e = big at hE
  -- seventeen digits always fit
  have h17 : (candidate M e lc incl (big - (17 : Nat) + 1)).isSome = true := by
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
  have hp := searchDigits_spec (fun p => (candidate M e lc incl (big - p + 1)).isSome) 5 1 17 h17
    (by decide) (by decide)
  unfold shortest
  simp only [hx, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hd]
  simp only [hM, ite_false, hlc, hincl, hbig]
  generalize searchDigits (fun p => (candidate M e lc incl (big - p + 1)).isSome) 5 1 17 = p at hp
  cases hc : candidate M e lc incl (big - p + 1) with
  | none => rw [hc] at hp; cases hp
  | some d =>
    simp only
    obtain ⟨j, hj1, hj2⟩ := stripZeros_spec 20 d (big - p + 1)
    generalize hs : stripZeros 20 d (big - p + 1) = sd at hj1 hj2
    obtain ⟨digits, exponent⟩ := sd
    simp only at hj1 hj2 ⊢
    refine ⟨_, rfl, rfl, ?_⟩
    have hf := candidate_fits hc
    rw [hj1, fits_scale] at hf
    rw [hj2]
    exact hf

end FloatText

end ExactJSON
