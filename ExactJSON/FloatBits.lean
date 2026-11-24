module

public import ExactJSON.Float

/-! # The bits of a finite float

Facts about the bit patterns of Lean's floats that reading floats back needs: a float is its bits
(`toBits_inj`), negating a finite float flips its sign bit and nothing else (`neg_toBits`), so
it keeps its significand and exponent and negating twice gives it back, and a finite float whose
significand is zero is `0.0` or `-0.0`.
-/

public section

namespace ExactJSON

namespace FloatText

open Float.Model Float.Model.UnpackedFloat

private theorem packComponents_toNat (s : Sign) (e : BitVec 11) (m : BitVec 52) :
    (packComponents Format.binary64 s e m).toNat = s.toBitVec.toNat * 2 ^ 63 + e.toNat * 2 ^ 52 + m.toNat := by
  unfold packComponents
  simp only [BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt e.isLt, ← Nat.shiftLeft_add_eq_or_of_lt m.isLt]
  simp only [Nat.shiftLeft_eq]
  omega

private theorem sign_neg_toNat (s : BitVec 1) : (-(Sign.ofBitVec s)).toBitVec.toNat = 1 - s.toNat := by
  revert s; decide

/-- Negating a finite float flips its sign bit. -/
theorem neg_toBits (x : Float) (hx : finiteFloat x = true) :
    (-x).toBits.toNat = (x.toBits.toNat + 2 ^ 63) % 2 ^ 64 := by
  have hdef : (-x).toBits = UInt64.ofBitVec (UnpackedFloat.pack Format.binary64
      (UnpackedFloat.unpack Format.binary64 x.toBits.toBitVec).neg) := rfl
  rw [hdef, UInt64.toNat_ofBitVec]
  unfold finiteFloat at hx
  rw [← UInt64.toNat_toBitVec] at hx ⊢
  generalize x.toBits.toBitVec = bv at hx ⊢
  have hlt := bv.isLt
  simp only [bne_iff_ne, ne_eq] at hx
  unfold UnpackedFloat.unpack
  simp only
  have he : (unpackExponent (spec := Format.binary64) bv).toNat = bv.toNat / 2 ^ 52 % 2 ^ 11 := by
    simp [unpackExponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hm : (unpackMantissa (spec := Format.binary64) bv).toNat = bv.toNat % 2 ^ 52 := by
    simp [unpackMantissa, BitVec.extractLsb'_toNat]
  have hs : (unpackSign (spec := Format.binary64) bv).toNat = bv.toNat / 2 ^ 63 % 2 := by
    simp [unpackSign, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have hsn := sign_neg_toNat (unpackSign (spec := Format.binary64) bv)
  split
  · rename_i h
    have := congrArg BitVec.toNat h
    simp only [he] at this
    simp at this
    omega
  · split
    · rename_i h0 h1
      split
      · rename_i h2
        have := congrArg BitVec.toNat h1
        have := congrArg BitVec.toNat h2
        simp only [he, hm] at *
        simp [UnpackedFloat.neg, UnpackedFloat.pack, packedZero, packComponents_toNat, hsn] at *
        omega
      · rename_i h2
        have := congrArg BitVec.toNat h1
        have h2' : ¬ (unpackMantissa (spec := Format.binary64) bv).toNat = 0 := fun h => h2 (BitVec.eq_of_toNat_eq h)
        simp only [he, hm] at *
        simp only [BitVec.toNat_ofNat, Nat.zero_mod] at this
        have hlog : (bv.toNat % 4503599627370496).log2 < 52 :=
          (Nat.log2_lt (by omega)).mpr (Nat.mod_lt _ (by decide))
        simp [UnpackedFloat.neg, UnpackedFloat.pack, Format.exponentBias, Format.mantissaBits]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), packComponents_toNat, hsn, hs]
        simp only [BitVec.toNat_ofNat]
        omega
    · rename_i h0 h1
      have e0 : ¬ (unpackExponent (spec := Format.binary64) bv).toNat = 2047 := fun h => h0 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      have e1 : ¬ (unpackExponent (spec := Format.binary64) bv).toNat = 0 := fun h => h1 (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
      simp only [he] at e0 e1
      simp [UnpackedFloat.neg, UnpackedFloat.pack, Format.exponentBias, Format.mantissaBits, hm, he]
      have hor : (4503599627370496 ||| bv.toNat % 4503599627370496) = 4503599627370496 + bv.toNat % 4503599627370496 := by
        have := Nat.shiftLeft_add_eq_or_of_lt (i := 52) (Nat.mod_lt bv.toNat (show 0 < 2 ^ 52 by decide)) 1
        simpa using this.symm
      have hlog : (4503599627370496 + bv.toNat % 4503599627370496).log2 = 52 := by
        have h1 := (Nat.le_log2 (n := 4503599627370496 + bv.toNat % 4503599627370496) (by omega)).mpr (by omega : 2 ^ 52 ≤ _)
        have h2 := (Nat.log2_lt (n := 4503599627370496 + bv.toNat % 4503599627370496) (by omega)).mpr (by omega : _ < 2 ^ 53)
        omega
      rw [hor, hlog]
      simp only [ite_true]
      rw [ite_eq_right (by omega), packComponents_toNat, hsn, hs]
      simp only [BitVec.toNat_ofNat]
      omega

/-- A float is its bits. -/
theorem toBits_inj {x y : Float} (h : x.toBits = y.toBits) : x = y := by
  cases x with | ofModel mx => cases y with | ofModel my =>
  cases mx; cases my
  simp only [Float.toBits] at h
  subst h; rfl

/-- The negation of a finite float is finite. -/
theorem finiteFloat_neg {x : Float} (hx : finiteFloat x = true) : finiteFloat (-x) = true := by
  have h := neg_toBits x hx
  unfold finiteFloat at hx ⊢
  simp only [bne_iff_ne, ne_eq] at hx ⊢
  have := x.toBits.toNat_lt
  rw [h]
  omega

/-- Negating a finite float flips its sign and keeps its significand and exponent. -/
theorem decompose_neg {x : Float} (hx : finiteFloat x = true) {s : Bool} {M : Nat} {e : Int}
    (hd : decompose x = (s, M, e)) : decompose (-x) = (!s, M, e) := by
  have h := neg_toBits x hx
  have hlt := x.toBits.toNat_lt
  unfold decompose at hd ⊢
  simp only at hd ⊢
  rw [h]
  have h1 : (x.toBits.toNat + 2 ^ 63) % 2 ^ 64 / 2 ^ 52 % 2 ^ 11 = x.toBits.toNat / 2 ^ 52 % 2 ^ 11 := by omega
  have h2 : (x.toBits.toNat + 2 ^ 63) % 2 ^ 64 % 2 ^ 52 = x.toBits.toNat % 2 ^ 52 := by omega
  have h3 : decide ((x.toBits.toNat + 2 ^ 63) % 2 ^ 64 ≥ 2 ^ 63) = !decide (x.toBits.toNat ≥ 2 ^ 63) := by
    by_cases h : x.toBits.toNat ≥ 2 ^ 63
    · simp only [h, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
    · simp only [h, decide_false, Bool.not_false, decide_eq_true_eq]; omega
  rw [h1, h2, h3]
  split
  all_goals (rename_i hb; split at hd)
  all_goals first
    | (simp only [Prod.mk.injEq] at hd; obtain ⟨rfl, rfl, rfl⟩ := hd; rfl)
    | omega

/-- Negating a finite float twice gives it back. -/
theorem neg_neg_of_finite {x : Float} (hx : finiteFloat x = true) : -(-x) = x := by
  apply toBits_inj
  apply UInt64.toNat_inj.mp
  rw [neg_toBits (-x) (finiteFloat_neg hx), neg_toBits x hx]
  have := x.toBits.toNat_lt
  omega

/-- A finite float whose significand is zero is a zero. -/
theorem eq_zero_of_decompose {x : Float} {s : Bool} {e : Int} (hd : decompose x = (s, 0, e)) :
    x = if s then -0.0 else 0.0 := by
  have hlt := x.toBits.toNat_lt
  unfold decompose at hd
  simp only at hd
  apply toBits_inj
  apply UInt64.toNat_inj.mp
  split at hd
  · simp only [Prod.mk.injEq] at hd
    obtain ⟨hs, hf, -⟩ := hd
    subst hs
    by_cases h : x.toBits.toNat ≥ 2 ^ 63
    · simp only [h, decide_true, ite_true]
      rw [show (-0.0 : Float).toBits.toNat = 2 ^ 63 by decide +kernel]
      omega
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]
      rw [show (0.0 : Float).toBits.toNat = 0 by decide +kernel]
      omega
  · simp only [Prod.mk.injEq] at hd
    omega

end FloatText

end ExactJSON
