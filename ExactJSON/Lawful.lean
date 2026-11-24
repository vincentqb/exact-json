module

public import ExactJSON.CodecLaws
public import ExactJSON.FloatSpecial

public section

namespace ExactJSON

universe u

theorem lawful_of_codec {α : Type u} [ToValue α] [FromValue α] {f : α → Value}
    (h : ∀ a, toValue a = f a ∧ ∀ w, fromValue? w = .ok a ↔ w = f a) (hv : ∀ a, (f a).Valid) : LawfulValue α :=
  ⟨fun a => ((h a).2 _).mpr (h a).1, fun a => (h a).1 ▸ hv a⟩

instance : LawfulValue String := lawful_of_codec codec_string fun _ => rfl
instance : LawfulValue Bool := lawful_of_codec codec_bool fun _ => rfl
instance : LawfulValue Int := lawful_of_codec codec_int fun _ => rfl
instance : LawfulValue Nat := lawful_of_codec codec_nat fun _ => rfl
instance : LawfulValue UInt8 := lawful_of_codec codec_uInt8 fun _ => rfl
instance : LawfulValue UInt16 := lawful_of_codec codec_uInt16 fun _ => rfl
instance : LawfulValue UInt32 := lawful_of_codec codec_uInt32 fun _ => rfl
instance : LawfulValue UInt64 := lawful_of_codec codec_uInt64 fun _ => rfl
instance : LawfulValue Int8 := lawful_of_codec codec_int8 fun _ => rfl
instance : LawfulValue Int16 := lawful_of_codec codec_int16 fun _ => rfl
instance : LawfulValue Int32 := lawful_of_codec codec_int32 fun _ => rfl
instance : LawfulValue Int64 := lawful_of_codec codec_int64 fun _ => rfl
instance : LawfulValue Char := lawful_of_codec codec_char fun _ => rfl

instance : LawfulValue Float where
  fromValue_toValue x := by
    obtain ⟨ht, hr⟩ := codec_float x
    apply (hr _).mpr
    rw [ht]
    by_cases hn : x.isNaN
    · rw [ite_eq_left hn]
      exact .inr (.inl ⟨rfl, FloatText.eq_nan_of_isNaN hn⟩)
    · rw [ite_eq_right hn]
      by_cases hi : x.isInf
      · rw [ite_eq_left hi]
        by_cases hp : x > 0
        · rw [ite_eq_left hp]
          exact .inr (.inr (.inl ⟨rfl, FloatText.eq_inf_of_isInf hi hp⟩))
        · rw [ite_eq_right hp]
          exact .inr (.inr (.inr ⟨rfl, FloatText.eq_neg_inf_of_isInf hi hp⟩))
      · rw [ite_eq_right hi]
        exact .inl rfl
  toValue_valid x := by
    rw [(codec_float x).1]
    by_cases hn : x.isNaN
    · rw [ite_eq_left hn]; rfl
    · rw [ite_eq_right hn]
      by_cases hi : x.isInf
      · rw [ite_eq_left hi]; split <;> rfl
      · rw [ite_eq_right hi]
        exact FloatText.finiteFloat_of_not (by simpa using hn) (by simpa using hi)

theorem mapM_toValue {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] :
    ∀ (xs : List α), (xs.map toValue).mapM fromValue? = .ok xs
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, List.mapM_cons, LawfulValue.fromValue_toValue, mapM_toValue xs]
    rfl

theorem itemsValid_toValue {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] :
    ∀ (xs : List α), itemsValid (xs.map toValue) = true
  | [] => rfl
  | x :: xs => by
    simp only [List.map_cons, itemsValid, LawfulValue.toValue_valid x, itemsValid_toValue xs, Bool.and_self]

instance {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] : LawfulValue (Array α) where
  fromValue_toValue xs := ((codec_array xs).2 _).mpr ⟨_, (codec_array xs).1, by simpa using mapM_toValue xs.toList⟩
  toValue_valid xs := by
    rw [(codec_array xs).1]
    simpa [Value.Valid, Value.isValid] using itemsValid_toValue xs.toList

instance {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] : LawfulValue (List α) where
  fromValue_toValue xs := ((codec_list xs).2 _).mpr ⟨_, (codec_list xs).1, by simpa using mapM_toValue xs⟩
  toValue_valid xs := by
    rw [(codec_list xs).1]
    simpa [Value.Valid, Value.isValid] using itemsValid_toValue xs

instance {α β : Type u} [ToValue α] [FromValue α] [LawfulValue α] [ToValue β] [FromValue β] [LawfulValue β] :
    LawfulValue (α × β) where
  fromValue_toValue p :=
    ((codec_prod p.1 p.2).2 _).mpr ⟨_, _, (codec_prod p.1 p.2).1, LawfulValue.fromValue_toValue p.1,
      LawfulValue.fromValue_toValue p.2⟩
  toValue_valid p := by
    rw [(codec_prod p.1 p.2).1]
    simp [Value.Valid, Value.isValid, itemsValid, LawfulValue.toValue_valid p.1, LawfulValue.toValue_valid p.2]

instance {α : Type u} [ToValue α] [FromValue α] [NotNull α] [LawfulValue α] : LawfulValue (Option α) where
  fromValue_toValue o := by
    apply ((codec_option o).2 _).mpr
    rw [(codec_option o).1]
    cases o with
    | none => rfl
    | some a => exact ⟨NotNull.toValue_ne_null a, LawfulValue.fromValue_toValue a⟩
  toValue_valid o := by
    rw [(codec_option o).1]
    cases o with
    | none => rfl
    | some a => exact LawfulValue.toValue_valid a

end ExactJSON
