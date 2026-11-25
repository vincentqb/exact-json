module

public import ExactJSON.Rfc8259
public import ExactJSON.Normalize

public section

namespace ExactJSON

theorem Rfc8259.numberValue_valid (token : List Char) (v : Value) (h : Rfc8259.numberValue token = .ok v) :
    v.isValid = true := by
  unfold Rfc8259.numberValue at h
  simp only at h
  repeat' (split at h <;> (try cases h))
  all_goals rfl

end ExactJSON
