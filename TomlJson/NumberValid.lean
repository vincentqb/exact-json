module

public import TomlJson.Rfc8259

/-! # What an RFC 8259 number holds is valid -/

public section

namespace TomlJson

/-- The float of a decimal, when there is one, is finite. -/
theorem Rfc8259.floatOf?_finite (negative : Bool) (m : Nat) (q : Int) (x : Float)
    (h : Rfc8259.floatOf? negative m q = some x) : finiteFloat x = true := by
  unfold Rfc8259.floatOf? at h
  simp only at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- What an RFC 8259 number holds is a valid value. -/
theorem Rfc8259.numberValue_valid (token : List Char) (v : Value) (h : Rfc8259.numberValue token = .ok v) :
    v.isValid = true := by
  unfold Rfc8259.numberValue at h
  simp only at h
  repeat' (split at h <;> (try cases h))
  all_goals first
    | rfl
    | (simp only [Value.isValid]; exact Rfc8259.floatOf?_finite _ _ _ _ (by assumption))

end TomlJson
