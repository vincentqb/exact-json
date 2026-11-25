module

public import ExactJSON.ShortestCore
public import ExactJSON.ReadBackExact

public section

namespace ExactJSON

namespace ShortestLaws

open FloatText

theorem floatOf?_of_roundsTo {x : Float} (hx : finiteFloat x = true) {s : Bool} {M : Nat} {e : Int}
    (hd : decompose x = (s, M, e)) (hM : M ≠ 0) {m : Nat} {q : Int}
    (h : roundsTo M e m q = true) : floatOf? s m q = some x := by
  obtain ⟨-, hr⟩ := decompose_spec x hx s M e hd
  obtain ⟨hr1, hr2⟩ := hr hM
  obtain ⟨hm0, hc1, hc2⟩ := interval_bounds M e hM hr1 hr2 _ _ _ _ h
  rw [floatOf?_eq _ _ _ hm0 hc1 hc2]
  cases s
  · have := ofScientificRounds x M e _ _ hx hd hM h
    simp only [Bool.false_eq_true, ite_false, this, hx, ite_true]
  · have := ofScientificRounds (-x) M e _ _ (finiteFloat_neg hx) (by rw [decompose_neg hx hd]; rfl) hM h
    simp only [ite_true, this, neg_neg_of_finite hx, hx]

theorem floatOf?_zero_eq (neg : Bool) : floatOf? neg 0 0 = some (if neg then -0.0 else 0.0) := by
  unfold floatOf?
  simp only [ite_true, Option.map]
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    rw [show finiteFloat 0.0 = true by decide +kernel]
    rfl
  · simp only [ite_true]
    rw [show finiteFloat (-0.0) = true by decide +kernel]
    rfl

theorem floatOf?_zero {x : Float} {neg : Bool} {e : Int}
    (hd : decompose x = (neg, 0, e)) : floatOf? neg 0 0 = some x := by
  rw [floatOf?_zero_eq, eq_zero_of_decompose hd]

theorem shortest_zero {x : Float} (hx : finiteFloat x = true) {neg : Bool} {e : Int}
    (hd : decompose x = (neg, 0, e)) : shortest x = some ⟨neg, 0, 0, by decide⟩ := by
  unfold shortest
  simp only [hx, Bool.not_true, Bool.false_eq_true, ite_false]
  rw [hd]
  rfl

theorem value_dist (d : Decimal) (x : Float) {neg : Bool} {M : Nat} {e : Int} (hd : decompose x = (neg, M, e))
    (hneg : d.negative = neg) :
    (d.value - floatValue x).abs = ((d.digits : Rat) * 10 ^ d.exponent - (M : Rat) * 2 ^ e).abs := by
  rw [floatValue_eq hd]
  unfold Decimal.value
  rw [hneg]
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    congr 1
    grind
  · simp only [ite_true]
    rw [show (-1 : Rat) * d.digits * 10 ^ d.exponent - -((M : Rat) * 2 ^ e) =
        -((d.digits : Rat) * 10 ^ d.exponent - (M : Rat) * 2 ^ e) by grind, Rat.abs_neg]

theorem floatValue_zero {x : Float} {neg : Bool} {e : Int} (hd : decompose x = (neg, 0, e)) : floatValue x = 0 := by
  rw [floatValue_eq hd]
  cases neg <;> simp

theorem rat_abs_zero_sub : ((0 : Rat) - 0).abs = 0 := by rw [Rat.sub_self, Rat.abs_zero]

theorem zero_digitCount (neg : Bool) : (⟨neg, 0, 0, by decide⟩ : Decimal).digitCount = 1 := by
  unfold Decimal.digitCount
  have h1 := (FloatText.digits_length_le_iff 0 1 (by decide)).mpr (by decide)
  have h2 := FloatText.digits_length_pos 0
  simp only at h1 h2 ⊢
  omega

theorem zero_value (neg : Bool) : (⟨neg, 0, 0, by decide⟩ : Decimal).value = 0 := by
  unfold Decimal.value; simp

theorem isShortest_zero {x : Float} {neg : Bool} {e : Int}
    (hd : decompose x = (neg, 0, e)) : (⟨neg, 0, 0, by decide⟩ : Decimal).IsShortest x := by
  refine ⟨floatOf?_zero hd, fun d' _ => ?_⟩
  rw [zero_digitCount, zero_value, floatValue_zero hd]
  have hn := FloatText.digits_length_pos d'.digits
  unfold Decimal.digitCount
  rcases Nat.lt_or_ge 1 (Nat.toDigits 10 d'.digits).length with h | h
  · exact Or.inl h
  · right
    refine ⟨by omega, ?_⟩
    rw [rat_abs_zero_sub]
    rcases Rat.le_iff_lt_or_eq.mp (Rat.abs_nonneg (x := d'.value - 0)) with h2 | h2
    · exact Or.inl h2
    · exact Or.inr ⟨h2, Or.inr rfl⟩

theorem decimal_eq {d D : Decimal} (h1 : d.negative = D.negative) (h2 : d.digits = D.digits)
    (h3 : d.exponent = D.exponent) : d = D :=
  Decimal.eq_of_parts h1 h2 h3

theorem shortest_isShortest (x : Float) (hx : finiteFloat x = true) (D : Decimal) (hs : shortest x = some D) :
    D.IsShortest x := by
  rcases hd : decompose x with ⟨neg, M, e⟩
  by_cases hM : M = 0
  · subst hM
    rw [shortest_zero hx hd, Option.some.injEq] at hs
    subst hs
    exact isShortest_zero hd
  · obtain ⟨D', hs', hneg, hfit, hall⟩ := shortest_strong x hx neg M e hd hM
    rw [hs, Option.some.injEq] at hs'
    subst hs'
    refine ⟨?_, ?_⟩
    · show floatOf? D.negative D.digits D.exponent = some x
      rw [hneg]
      exact floatOf?_of_roundsTo hx hd hM hfit
    · intro d' hd'
      obtain ⟨hn', hr'⟩ := floatOf?_sound hx hd hM hd'
      unfold Decimal.digitCount
      rw [value_dist D x hd hneg, value_dist d' x hd hn']
      rcases hall d'.digits d'.exponent hr' with h | ⟨h1, h | ⟨h2, h3⟩⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, Or.inl h⟩
      · refine Or.inr ⟨h1, Or.inr ⟨h2, ?_⟩⟩
        rcases h3 with ⟨e1, e2⟩ | ⟨e1, -⟩
        · exact Or.inl (decimal_eq (hn'.trans hneg.symm) e1 e2)
        · exact Or.inr e1

theorem shortest_isSome (x : Float) (hx : finiteFloat x = true) : ∃ D, shortest x = some D := by
  rcases hd : decompose x with ⟨neg, M, e⟩
  by_cases hM : M = 0
  · subst hM
    exact ⟨_, shortest_zero hx hd⟩
  · obtain ⟨D, hs, -⟩ := shortest_strong x hx neg M e hd hM
    exact ⟨D, hs⟩

theorem floatsReadBack (x : Float) (hx : finiteFloat x = true) (dd : Decimal) (hs : shortest x = some dd) :
    floatOf? dd.negative dd.digits dd.exponent = some x := by
  rcases hd : decompose x with ⟨neg, M, e⟩
  by_cases hM : M = 0
  · subst hM
    rw [shortest_zero hx hd] at hs
    cases hs
    exact floatOf?_zero hd
  · obtain ⟨D, hs', hneg, hround, -⟩ := shortest_strong x hx neg M e hd hM
    rw [hs] at hs'
    cases hs'
    rw [hneg]
    exact floatOf?_of_roundsTo hx hd hM hround

end ShortestLaws

open FloatText ShortestLaws

end ExactJSON
