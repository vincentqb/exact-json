module

public import ExactJSON.Rfc8259

/-! # Exact conversions between `Float` and decimal text

A finite `Float` (IEEE 754 binary64) is printed as the *shortest* decimal that reads back as the
same `Float`, and among the shortest, the one closest to it (ties to an even last digit). This is
the digit string that Python's `repr`, JavaScript's `Number.prototype.toString` and Ryu produce;
the arithmetic is exact (on `Nat`), so there is no rounding in the printer itself.

Lean's own `Float.toString` prints six fixed decimals (`1e-7` prints as `0.000000`), which is why
this module exists.

Reading decimal text uses `Float.ofScientific`, which rounds correctly (to nearest, ties to even),
after bounding the decimal exponent so that an absurd exponent (`1e999999999`) costs nothing; the
arithmetic on a number's digits is still quadratic in how many there are.
-/

@[expose] public section

namespace ExactJSON

/-- A decimal number `(-1)^negative × digits × 10^exponent`. The canonical form of a nonzero
value has no trailing zero in `digits`; zero is `digits = 0, exponent = 0`. -/
structure Decimal where
  /-- The sign; `true` for `-0.0` as well. -/
  negative : Bool
  /-- The significand's digits, as a natural number. -/
  digits : Nat
  /-- The power of ten the digits are scaled by. -/
  exponent : Int
  deriving DecidableEq, Repr, Inhabited

namespace Decimal

/-- `n` zeros. -/
def zeros (n : Nat) : List Char := List.replicate n '0'

/-- The canonical text of a decimal read as a float: at least one digit after the point, no other
superfluous character. Fixed notation when the scientific exponent is in `[-4, 16)` (as Python's
`repr`), otherwise `d.ddd` + `e` + exponent with no `+` and no leading zeros. Examples: `0.0`,
`-0.0`, `1.0`, `0.1`, `123.456`, `0.0001`, `1.0e-5`, `1.0e16`, `5.0e-324`. -/
def toFloatText (d : Decimal) : String :=
  let sign : List Char := if d.negative then ['-'] else []
  if d.digits = 0 then String.ofList (sign ++ "0.0".toList)
  else
    let ds := Nat.toDigits 10 d.digits
    let n := ds.length
    let sci : Int := d.exponent + n - 1
    let body : List Char :=
      if -4 ≤ sci ∧ sci < 16 then
        if sci ≥ n - 1 then ds ++ zeros (sci - (n - 1) : Int).toNat ++ ['.', '0']
        else if 0 ≤ sci then ds.take (sci.toNat + 1) ++ ['.'] ++ ds.drop (sci.toNat + 1)
        else ['0', '.'] ++ zeros ((-sci).toNat - 1) ++ ds
      else
        ds.take 1 ++ ['.'] ++ (if n = 1 then ['0'] else ds.drop 1) ++ ['e'] ++ (toString sci).toList
    String.ofList (sign ++ body)

end Decimal

namespace FloatText

/-- `a ^ k` for an integer `k`, split as numerator and denominator: `(a ^ max k 0, a ^ max (-k) 0)`. -/
def powSplit (a : Nat) (k : Int) : Nat × Nat :=
  if 0 ≤ k then (a ^ k.toNat, 1) else (1, a ^ (-k).toNat)

/-- The sign, significand and binary exponent of a finite float: `x = (-1)^s × m × 2^e`. -/
def decompose (x : Float) : Bool × Nat × Int :=
  let bits : Nat := x.toBits.toNat
  let negative := bits ≥ 2 ^ 63
  let biased : Nat := bits / 2 ^ 52 % 2 ^ 11
  let fraction : Nat := bits % 2 ^ 52
  if biased = 0 then (negative, fraction, -1074)
  else (negative, fraction + 2 ^ 52, (biased : Int) - 1075)

/-- Whether `10 ^ k ≤ m × 2 ^ e`, exactly. -/
def tenPowLe (k : Int) (m : Nat) (e : Int) : Bool :=
  let (tn, td) := powSplit 10 k
  let (bn, bd) := powSplit 2 e
  tn * bd ≤ m * bn * td

/-- `k`, lowered while `10 ^ k > m × 2 ^ e`, at most `n` times. -/
def lowerExponent (m : Nat) (e : Int) : Nat → Int → Int
  | 0, k => k
  | n + 1, k => if tenPowLe k m e then k else lowerExponent m e n (k - 1)

/-- `k`, raised while `10 ^ (k + 1) ≤ m × 2 ^ e`, at most `n` times. -/
def raiseExponent (m : Nat) (e : Int) : Nat → Int → Int
  | 0, k => k
  | n + 1, k => if tenPowLe (k + 1) m e then raiseExponent m e n (k + 1) else k

/-- `⌊log₁₀ (m × 2 ^ e)⌋` for `m > 0`, by an estimate corrected with exact comparisons. -/
def decimalExponent (m : Nat) (e : Int) : Int :=
  -- log₁₀ 2 ≈ 78913 / 2^18; the estimate is off by at most one either way.
  let log2 : Int := (Nat.log2 m : Int) + e
  raiseExponent m e 4 (lowerExponent m e 4 ((log2 * 78913) / 262144))

/-- The interval of reals that round to `m × 2 ^ e` (the float with significand `m`, binary
exponent `e`, and the boundary flag `lowerCloser` when the next float down is closer), scaled by
`2 ^ (2 - e)`: `(low, x, high)`, every one an integer. -/
def roundingInterval (m : Nat) (lowerCloser : Bool) : Nat × Nat × Nat :=
  (if lowerCloser then 4 * m - 1 else 4 * m - 2, 4 * m, 4 * m + 2)

/-- The scale `(a, b)` of a candidate for `m × 2 ^ e` at `10 ^ k`: a multiple `y` of `2 ^ (e - 2)`
is `y × a / b` units of `10 ^ k`. -/
def scale (e k : Int) : Nat × Nat :=
  let (a2, b2) := powSplit 2 (e - 2)
  let (b10, a10) := powSplit 10 k
  (a2 * a10, b2 * b10)

/-- Whether `d` units of `10 ^ k` lie between `low` and `high` multiples of `2 ^ (e - 2)`, at
scale `(a, b)` (`scale e k`), the ends included when `inclusive`. -/
def fits (low high a b : Nat) (inclusive : Bool) (d : Nat) : Bool :=
  let v := d * b
  (low * a < v || (inclusive && low * a == v)) && (v < high * a || (inclusive && v == high * a))

/-- The `p`-digit decimal significand nearest `m × 2^e` that still reads back as it, if any:
`d` with `d × 10 ^ k` in the rounding interval, for `k = E - p + 1` where `E` is the decimal
exponent. -/
def candidate (m : Nat) (e : Int) (lowerCloser inclusive : Bool) (k : Int) :
    Option Nat :=
  let (low, x, high) := roundingInterval m lowerCloser
  -- The scaled values are multiples of `2 ^ (e - 2)`; divide by `10 ^ k` as `· × a / b`.
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

/-- The least `p` in `[lo, hi]` with `cand p`, halving the range `n` times, when `cand` is monotone
and true at `hi`. -/
def searchDigits (cand : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | n + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if cand mid then searchDigits cand n lo mid else searchDigits cand n (mid + 1) hi
    else lo

/-- `d × 10 ^ x` with at most `n` trailing zeros of `d` moved into the exponent. -/
def stripZeros : Nat → Nat → Int → Nat × Int
  | 0, d, x => (d, x)
  | n + 1, d, x => if d != 0 && d % 10 == 0 then stripZeros n (d / 10) (x + 1) else (d, x)

/-- The shortest decimal that reads back as `x`, closest to `x` among the shortest; `none` for a
NaN or an infinity. -/
def shortest (x : Float) : Option Decimal :=
  if !finiteFloat x then none
  else
    let (negative, m, e) := decompose x
    if m = 0 then some { negative, digits := 0, exponent := 0 }
    else
      -- Round half to even when reading: the interval's ends belong to `x` when `m` is even.
      let inclusive := m % 2 == 0
      -- At a power of two (other than the least normal one) the float below is half as far.
      let lowerCloser := m = 2 ^ 52 && e > -1074
      let big := decimalExponent m e
      let cand (p : Nat) := candidate m e lowerCloser inclusive (big - p + 1)
      -- `p ↦ (cand p).isSome` is monotone and true at 17: search for its least `p`, halving
      -- `[1, 17]` five times.
      let p := searchDigits (fun p => (cand p).isSome) 5 1 17
      match cand p with
      | none => none  -- unreachable: 17 digits always suffice
      | some d =>
        -- at most 18 trailing zeros (17 digits, rounded up to a power of ten)
        let (digits, exponent) := stripZeros 20 d (big - p + 1)
        some { negative, digits, exponent }

/-- The float nearest `(-1)^negative × m × 10^q`, rounding ties to even, or `none` when that is
an infinity (`Rfc8259.floatOf?`). -/
def ofDecimal? (negative : Bool) (m : Nat) (q : Int) : Option Float := Rfc8259.floatOf? negative m q

end FloatText

/-- The canonical text of a finite float (see `Decimal.toFloatText`), `none` for a NaN or an
infinity. -/
def Float.toCanonical? (x : Float) : Option String :=
  (FloatText.shortest x).map Decimal.toFloatText

end ExactJSON
