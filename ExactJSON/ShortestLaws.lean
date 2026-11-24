module

public import ExactJSON.ShortestCore
public import ExactJSON.ReadBackExact
public import ExactJSON.RenderInjective
public import ExactJSON.LeanJson
import all ExactJSON.LeanJson

public section

namespace ExactJSON

namespace ShortestLaws

open FloatText

theorem floatOf?_of_roundsTo {x : Float} (hx : finiteFloat x = true) {s : Bool} {M : Nat} {e : Int}
    (hd : decompose x = (s, M, e)) (hM : M ≠ 0) {m : Nat} {q : Int}
    (h : roundsTo M e m q = true) : Rfc8259.floatOf? s m q = some x := by
  obtain ⟨-, hr⟩ := decompose_spec x hx s M e hd
  obtain ⟨hr1, hr2⟩ := hr hM
  obtain ⟨hm0, hc1, hc2⟩ := interval_bounds M e hM hr1 hr2 _ _ _ _ h
  rw [floatOf?_eq _ _ _ hm0 hc1 hc2]
  cases s
  · have := ofScientificRounds x M e _ _ hx hd hM h
    simp only [Bool.false_eq_true, ite_false, this, hx, ite_true]
  · have := ofScientificRounds (-x) M e _ _ (finiteFloat_neg hx) (by rw [decompose_neg hx hd]; rfl) hM h
    simp only [ite_true, this, neg_neg_of_finite hx, hx]

theorem finite_of_floatOf? {neg : Bool} {m : Nat} {q : Int} {x : Float} (h : Rfc8259.floatOf? neg m q = some x) :
    finiteFloat x = true := by
  unfold Rfc8259.floatOf? at h
  simp only at h
  split at h
  · split at h
    · rename_i hf; simp only [Option.some.injEq] at h; subst h; exact hf
    · cases h
  · cases h

theorem floatOf?_zero_eq (neg : Bool) : Rfc8259.floatOf? neg 0 0 = some (if neg then -0.0 else 0.0) := by
  unfold Rfc8259.floatOf?
  simp only [ite_true, Option.map]
  cases neg
  · simp only [Bool.false_eq_true, ite_false]
    rw [show finiteFloat 0.0 = true by decide +kernel]
    rfl
  · simp only [ite_true]
    rw [show finiteFloat (-0.0) = true by decide +kernel]
    rfl

theorem floatOf?_zero {x : Float} {neg : Bool} {e : Int}
    (hd : decompose x = (neg, 0, e)) : Rfc8259.floatOf? neg 0 0 = some x := by
  rw [floatOf?_zero_eq, eq_zero_of_decompose hd]

theorem shortest_zero {x : Float} (hx : finiteFloat x = true) {neg : Bool} {e : Int}
    (hd : decompose x = (neg, 0, e)) : shortest x = some ⟨neg, 0, 0⟩ := by
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

theorem digits_zero_of_value {d : Decimal} (h : d.value = 0) : d.digits = 0 := by
  apply Classical.byContradiction
  intro hne
  have hpos : (0 : Rat) < (d.digits : Rat) * 10 ^ d.exponent :=
    Rat.mul_pos (natCast_pos' (Nat.pos_of_ne_zero hne)) (ten_zpow_pos _)
  unfold Decimal.value at h
  split at h <;> grind

theorem neg_zero_ne_zero : (-0.0 : Float) ≠ 0.0 := by
  intro h
  have := congrArg (fun y : Float => y.toBits.toNat) h
  rw [show (-0.0 : Float).toBits.toNat = 2 ^ 63 by decide +kernel,
    show (0.0 : Float).toBits.toNat = 0 by decide +kernel] at this
  cases this

theorem rat_abs_zero_sub : ((0 : Rat) - 0).abs = 0 := by rw [Rat.sub_self, Rat.abs_zero]

theorem zero_digitCount (neg : Bool) : (⟨neg, 0, 0⟩ : Decimal).digitCount = 1 := by
  unfold Decimal.digitCount
  have h1 := (FloatText.digits_length_le_iff 0 1 (by decide)).mpr (by decide)
  have h2 := FloatText.digits_length_pos 0
  simp only at h1 h2 ⊢
  omega

theorem zero_value (neg : Bool) : (⟨neg, 0, 0⟩ : Decimal).value = 0 := by
  unfold Decimal.value; simp

theorem isShortest_zero {x : Float} {neg : Bool} {e : Int}
    (hd : decompose x = (neg, 0, e)) : (⟨neg, 0, 0⟩ : Decimal).IsShortest x := by
  refine ⟨floatOf?_zero hd, fun _ => rfl, fun d' _ => ?_⟩
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
    (h3 : d.exponent = D.exponent) : d = D := by
  cases d
  cases D
  simp only at h1 h2 h3
  rw [h1, h2, h3]

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
    refine ⟨?_, ?_, ?_⟩
    · show Rfc8259.floatOf? D.negative D.digits D.exponent = some x
      rw [hneg]
      exact floatOf?_of_roundsTo hx hd hM hfit
    · intro h0
      exfalso
      obtain ⟨-, hr⟩ := decompose_spec x hx neg M e hd
      obtain ⟨hr1, hr2⟩ := hr hM
      exact (interval_bounds M e hM hr1 hr2 _ _ _ _ hfit).1 h0
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

theorem render_float_text (x : Float) : (Value.float x).render = floatText x := by
  simp [Value.render, Value.renderTo]

theorem shortest_unique (x : Float) (d : Decimal) (h : d.IsShortest x) : shortest x = some d := by
  have hx := finite_of_floatOf? h.1
  rcases hd : decompose x with ⟨neg, M, e⟩
  by_cases hM : M = 0
  · subst hM
    rw [shortest_zero hx hd]
    have hD := isShortest_zero hd
    have hdist : (d.value - 0).abs = 0 := by
      rcases h.2.2 _ hD.1 with h' | ⟨-, h' | ⟨h', -⟩⟩
      · rw [zero_digitCount] at h'
        have := FloatText.digits_length_pos d.digits
        unfold Decimal.digitCount at h'
        omega
      · rw [zero_value, floatValue_zero hd, rat_abs_zero_sub] at h'
        exact absurd h' (Rat.not_lt.mpr Rat.abs_nonneg)
      · rw [zero_value, floatValue_zero hd, rat_abs_zero_sub] at h'
        exact h'
    rw [Rat.abs_eq_zero_iff] at hdist
    have hval : d.value = 0 := by grind
    have hdig := digits_zero_of_value hval
    have hexp := h.2.1 hdig
    have hread := h.1
    unfold Decimal.ReadsBack at hread
    rw [hdig, hexp, floatOf?_zero_eq, eq_zero_of_decompose hd, Option.some.injEq] at hread
    have hneg : d.negative = neg := by
      cases hn : d.negative <;> cases neg <;> rw [hn] at hread <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] at hread
      all_goals first | rfl | exact absurd hread neg_zero_ne_zero | exact absurd hread.symm neg_zero_ne_zero
    rw [decimal_eq (D := ⟨neg, 0, 0⟩) hneg hdig hexp]
  · obtain ⟨D, hs, hneg, hfit, hall⟩ := shortest_strong x hx neg M e hd hM
    rw [hs]
    have hD := shortest_isShortest x hx D hs
    obtain ⟨hn', hr'⟩ := floatOf?_sound hx hd hM h.1
    have hc1 := hall d.digits d.exponent hr'
    have hc2 := h.2.2 D hD.1
    unfold Decimal.digitCount at hc2
    rw [value_dist D x hd hneg, value_dist d x hd hn'] at hc2
    generalize (Nat.toDigits 10 D.digits).length = nD at hc1 hc2
    generalize (Nat.toDigits 10 d.digits).length = nd at hc1 hc2
    generalize ((D.digits : Rat) * 10 ^ D.exponent - (M : Rat) * 2 ^ e).abs = A at hc1 hc2
    generalize ((d.digits : Rat) * 10 ^ d.exponent - (M : Rat) * 2 ^ e).abs = B at hc1 hc2
    rcases hc1 with g | ⟨g1, g | ⟨g2, g3⟩⟩ <;> rcases hc2 with f | ⟨f1, f | ⟨f2, f3⟩⟩
    all_goals first | omega | (exfalso; grind) | skip
    rcases f3 with f3 | f3
    · rw [f3]
    · rcases g3 with ⟨e1, e2⟩ | ⟨-, g3⟩
      · rw [decimal_eq (hneg.trans hn'.symm) e1.symm e2.symm]
      · omega

end ShortestLaws

open FloatText ShortestLaws

theorem render_float (x : Float) (hx : finiteFloat x = true) :
    ∃ d : Decimal, (Value.float x).render = d.toFloatText ∧ d.IsShortest x := by
  obtain ⟨D, hs⟩ := shortest_isSome x hx
  exact ⟨D, by rw [render_float_text, floatText_of_shortest hs], shortest_isShortest x hx D hs⟩

theorem floatToJson_finite (x : Float) (d : Decimal) (h : d.IsShortest x) :
    floatToJson x = .num d.toJsonNumber := by
  unfold floatToJson
  rw [shortest_unique x d h]
  unfold Decimal.toJsonNumber
  by_cases hc : d.exponent < 0 <;> simp only [hc, ↓reduceIte]

theorem parse_render_invalid (v : Value) (h : ¬ v.Valid) : (Value.parse v.render).toOption = none :=
  parse_render_invalid_of v h

end ExactJSON
