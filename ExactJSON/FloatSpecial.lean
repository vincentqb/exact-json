module

public import ExactJSON.FloatBits

public section

namespace ExactJSON

namespace FloatText

open Float.Model Float.Model.UnpackedFloat

private theorem toNat_unpackExponent (b : BitVec 64) :
    (unpackExponent (spec := Format.binary64) b).toNat = b.toNat / 2 ^ 52 % 2 ^ 11 := by
  simp [unpackExponent, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

private theorem toNat_unpackMantissa (b : BitVec 64) :
    (unpackMantissa (spec := Format.binary64) b).toNat = b.toNat % 2 ^ 52 := by
  simp [unpackMantissa, BitVec.extractLsb'_toNat]

private theorem unpack_isNaN {b : BitVec 64}
    (h : (UnpackedFloat.unpack Format.binary64 b).isNaN = true) :
    unpackExponent (spec := Format.binary64) b = -1#11 ∧
      unpackMantissa (spec := Format.binary64) b ≠ 0#52 := by
  unfold UnpackedFloat.unpack at h
  simp only at h
  split at h
  · rename_i he
    split at h
    · simp [UnpackedFloat.isNaN] at h
    · rename_i hm
      exact ⟨he, hm⟩
  · split at h
    · split at h <;> simp [UnpackedFloat.isNaN] at h
    · simp [UnpackedFloat.isNaN] at h

private theorem unpack_isInf {b : BitVec 64}
    (h : (UnpackedFloat.unpack Format.binary64 b).isInf = true) :
    unpackExponent (spec := Format.binary64) b = -1#11 ∧
      unpackMantissa (spec := Format.binary64) b = 0#52 := by
  unfold UnpackedFloat.unpack at h
  simp only at h
  split at h
  · rename_i he
    split at h
    · rename_i hm
      exact ⟨he, hm⟩
    · simp [UnpackedFloat.isInf] at h
  · split at h
    · split at h <;> simp [UnpackedFloat.isInf] at h
    · simp [UnpackedFloat.isInf] at h

private theorem isNaN_or_isInf {b : BitVec 64}
    (he : unpackExponent (spec := Format.binary64) b = -1#11) :
    (UnpackedFloat.unpack Format.binary64 b).isNaN = true ∨
      (UnpackedFloat.unpack Format.binary64 b).isInf = true := by
  by_cases hm : unpackMantissa (spec := Format.binary64) b = 0#52
  · exact .inr (by simp [UnpackedFloat.unpack, he, hm, UnpackedFloat.isInf])
  · exact .inl (by simp [UnpackedFloat.unpack, he, hm, UnpackedFloat.isNaN])

private theorem eq_inf_or_eq_neg_inf {x : Float} (h : x.isInf = true) :
    x = Float.inf ∨ x = -Float.inf := by
  obtain ⟨he, hm⟩ := unpack_isInf h
  have he := congrArg BitVec.toNat he
  have hm := congrArg BitVec.toNat hm
  rw [toNat_unpackExponent, show (-1#11 : BitVec 11).toNat = 2047 from rfl] at he
  rw [toNat_unpackMantissa, show (0#52 : BitVec 52).toNat = 0 from rfl] at hm
  have hlt := x.toModel.toBits.toBitVec.isLt
  have hinf : Float.inf.toBits.toNat = 2047 * 2 ^ 52 := by decide +kernel
  have hninf : (-Float.inf).toBits.toNat = 2 ^ 63 + 2047 * 2 ^ 52 := by decide +kernel
  rcases (by omega : x.toModel.toBits.toBitVec.toNat = 2047 * 2 ^ 52 ∨
      x.toModel.toBits.toBitVec.toNat = 2 ^ 63 + 2047 * 2 ^ 52) with hx | hx
  · exact .inl (toBits_inj (UInt64.toNat_inj.mp (hx.trans hinf.symm)))
  · exact .inr (toBits_inj (UInt64.toNat_inj.mp (hx.trans hninf.symm)))

theorem eq_nan_of_isNaN {x : Float} (h : x.isNaN = true) : x = Float.nan := by
  obtain ⟨he, hm⟩ := unpack_isNaN h
  exact toBits_inj (UInt64.eq_of_toBitVec_eq (x.toModel.valid.eq_packedNaN he hm))

theorem eq_inf_of_isInf {x : Float} (h : x.isInf = true) (hp : x > 0) : x = Float.inf := by
  rcases eq_inf_or_eq_neg_inf h with hx | hx
  · exact hx
  · subst hx
    exact absurd hp (by decide +kernel)

theorem eq_neg_inf_of_isInf {x : Float} (h : x.isInf = true) (hp : ¬ x > 0) : x = -Float.inf := by
  rcases eq_inf_or_eq_neg_inf h with hx | hx
  · subst hx
    exact absurd (by decide +kernel) hp
  · exact hx

theorem finiteFloat_of_not {x : Float} (hn : x.isNaN = false) (hi : x.isInf = false) :
    finiteFloat x = true := by
  unfold finiteFloat
  rw [bne_iff_ne]
  intro he
  have he : unpackExponent (spec := Format.binary64) x.toModel.toBits.toBitVec = -1#11 := by
    apply BitVec.eq_of_toNat_eq
    rw [toNat_unpackExponent, show (-1#11 : BitVec 11).toNat = 2047 from rfl]
    exact he
  rcases isNaN_or_isInf he with h | h
  · exact Bool.false_ne_true (hn.symm.trans h)
  · exact Bool.false_ne_true (hi.symm.trans h)

end FloatText

end ExactJSON
