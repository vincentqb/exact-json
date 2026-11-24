module

public import ExactJSON.Canonical

@[expose] public section

namespace ExactJSON

namespace FloatText

def powSplit (a : Nat) (k : Int) : Nat × Nat :=
  if 0 ≤ k then (a ^ k.toNat, 1) else (1, a ^ (-k).toNat)

def decompose (x : Float) : Bool × Nat × Int :=
  let bits : Nat := x.toBits.toNat
  let negative := bits ≥ 2 ^ 63
  let biased : Nat := bits / 2 ^ 52 % 2 ^ 11
  let fraction : Nat := bits % 2 ^ 52
  if biased = 0 then (negative, fraction, -1074)
  else (negative, fraction + 2 ^ 52, (biased : Int) - 1075)

def tenPowLe (k : Int) (m : Nat) (e : Int) : Bool :=
  let (tn, td) := powSplit 10 k
  let (bn, bd) := powSplit 2 e
  tn * bd ≤ m * bn * td

def lowerExponent (m : Nat) (e : Int) : Nat → Int → Int
  | 0, k => k
  | n + 1, k => if tenPowLe k m e then k else lowerExponent m e n (k - 1)

def raiseExponent (m : Nat) (e : Int) : Nat → Int → Int
  | 0, k => k
  | n + 1, k => if tenPowLe (k + 1) m e then raiseExponent m e n (k + 1) else k

def decimalExponent (m : Nat) (e : Int) : Int :=
  let log2 : Int := (Nat.log2 m : Int) + e
  raiseExponent m e 4 (lowerExponent m e 4 ((log2 * 78913) / 262144))

def roundingInterval (m : Nat) (lowerCloser : Bool) : Nat × Nat × Nat :=
  (if lowerCloser then 4 * m - 1 else 4 * m - 2, 4 * m, 4 * m + 2)

def scale (e k : Int) : Nat × Nat :=
  let (a2, b2) := powSplit 2 (e - 2)
  let (b10, a10) := powSplit 10 k
  (a2 * a10, b2 * b10)

def fits (low high a b : Nat) (inclusive : Bool) (d : Nat) : Bool :=
  let v := d * b
  (low * a < v || (inclusive && low * a == v)) && (v < high * a || (inclusive && v == high * a))

def candidate (m : Nat) (e : Int) (lowerCloser inclusive : Bool) (k : Int) :
    Option Nat :=
  let (low, x, high) := roundingInterval m lowerCloser
  let (a, b) := scale e k
  let xa := x * a
  let fits := fits low high a b inclusive
  let d0 := xa / b
  let d1 := d0 + 1
  match fits d0, fits d1 with
  | true, true =>
    let below := xa - d0 * b
    let above := d1 * b - xa
    if below < above then some d0
    else if above < below then some d1
    else if d0 % 2 == 0 then some d0 else some d1
  | true, false => some d0
  | false, true => some d1
  | false, false => none

def searchDigits (cand : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | n + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if cand mid then searchDigits cand n lo mid else searchDigits cand n (mid + 1) hi
    else lo

def stripZeros : Nat → Nat → Int → Nat × Int
  | 0, d, x => (d, x)
  | n + 1, d, x => if d != 0 && d % 10 == 0 then stripZeros n (d / 10) (x + 1) else (d, x)

def shortest (x : Float) : Option Decimal :=
  if !finiteFloat x then none
  else
    let (negative, m, e) := decompose x
    if m = 0 then some { negative, digits := 0, exponent := 0 }
    else
      let inclusive := m % 2 == 0
      let lowerCloser := m = 2 ^ 52 && e > -1074
      let big := decimalExponent m e
      let cand (p : Nat) := candidate m e lowerCloser inclusive (big - p + 1)
      let p := searchDigits (fun p => (cand p).isSome) 5 1 17
      match cand p with
      | none => none
      | some d =>
        let (digits, exponent) := stripZeros 20 d (big - p + 1)
        some { negative, digits, exponent }

def ofDecimal? (negative : Bool) (m : Nat) (q : Int) : Option Float := Rfc8259.floatOf? negative m q

end FloatText

def Float.toCanonical? (x : Float) : Option String :=
  (FloatText.shortest x).map Decimal.toFloatText

end ExactJSON
