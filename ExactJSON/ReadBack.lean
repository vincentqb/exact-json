module

public import ExactJSON.Shortest
public import ExactJSON.FloatBits
public import ExactJSON.SpecRender

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

end ExactJSON
