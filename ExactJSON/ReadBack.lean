module

public import ExactJSON.Shortest
public import ExactJSON.FloatBits
public import ExactJSON.Fixed

public section

namespace ExactJSON

universe u

open FloatText

theorem floatOf?_eq (neg : Bool) (m : Nat) (q : Int) (hm : m ≠ 0)
    (h1 : -324 ≤ ((Nat.toDigits 10 m).length : Int) + q) (h2 : ((Nat.toDigits 10 m).length : Int) + q ≤ 309) :
    Rfc8259.floatOf? neg m q =
      let y := if neg then -Float.ofScientific m (decide (q < 0)) q.natAbs else Float.ofScientific m (decide (q < 0)) q.natAbs
      if finiteFloat y then some y else none := by
  unfold Rfc8259.floatOf?
  simp only [hm, ite_false, show ¬ (((Nat.toDigits 10 m).length : Int) + q > 309) by omega,
    show ¬ (((Nat.toDigits 10 m).length : Int) + q < -324) by omega, Option.map]

@[expose] def FloatText.roundsTo (M : Nat) (e : Int) (m : Nat) (q : Int) : Bool :=
  let lowerCloser := decide (M = 2 ^ 52) && decide (e > -1074)
  FloatText.fits (FloatText.roundingInterval M lowerCloser).1 (FloatText.roundingInterval M lowerCloser).2.2
    (FloatText.scale e q).1 (FloatText.scale e q).2 (M % 2 == 0) m

@[expose] def OfScientificRounds : Prop :=
  ∀ (x : Float) (M : Nat) (e : Int) (m : Nat) (q : Int), finiteFloat x = true →
    FloatText.decompose x = (false, M, e) → M ≠ 0 → FloatText.roundsTo M e m q = true →
    Float.ofScientific m (decide (q < 0)) q.natAbs = x

theorem floatsReadBack (rounds : OfScientificRounds) (x : Float) (hx : finiteFloat x = true) (dd : Decimal)
    (hs : shortest x = some dd) : Rfc8259.floatOf? dd.negative dd.digits dd.exponent = some x := by
  rcases hd : decompose x with ⟨neg, M, e⟩
  by_cases hM : M = 0
  · subst hM
    have hz := eq_zero_of_decompose hd
    have hs' : shortest x = some ⟨neg, 0, 0⟩ := by
      unfold shortest
      simp only [hx, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hd]
      rfl
    rw [hs] at hs'
    cases hs'
    rw [hz]
    unfold Rfc8259.floatOf?
    simp only [ite_true, Option.map]
    cases neg
    · simp only [Bool.false_eq_true, ite_false]
      rw [show finiteFloat 0.0 = true by decide +kernel]
      rfl
    · simp only [ite_true]
      rw [show finiteFloat (-0.0) = true by decide +kernel]
      rfl
  · obtain ⟨-, hr⟩ := decompose_spec x hx neg M e hd
    obtain ⟨hr1, hr2⟩ := hr hM
    obtain ⟨dd', hs', hneg, hfit⟩ := shortest_spec x hx neg M e hd hM
    rw [hs] at hs'
    cases hs'
    obtain ⟨hm0, hc1, hc2⟩ := interval_bounds M e hM hr1 hr2 _ _ _ _ hfit
    have hround : roundsTo M e dd.digits dd.exponent = true := hfit
    rw [floatOf?_eq _ _ _ hm0 hc1 hc2, hneg]
    cases neg
    · have := rounds x M e _ _ hx hd hM hround
      simp only [Bool.false_eq_true, ite_false, this, hx, ite_true]
    · have := rounds (-x) M e _ _ (finiteFloat_neg hx) (by rw [decompose_neg hx hd]; rfl) hM hround
      simp only [ite_true, this, neg_neg_of_finite hx, hx]

end ExactJSON
