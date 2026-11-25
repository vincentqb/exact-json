module

public import ExactJSON.ShortestLaws
public import ExactJSON.FloatSpecial

public section

namespace ExactJSON

open FloatText ShortestLaws

private theorem pure_eq_ok {α : Type} (a : α) : (pure a : Except String α) = .ok a := rfl

theorem finiteFloat_of_isNaN {x : Float} (h : x.isNaN = true) : finiteFloat x = false := by
  rw [eq_nan_of_isNaN h]
  decide +kernel

theorem finiteFloat_of_isInf {x : Float} (h : x.isInf = true) : finiteFloat x = false := by
  by_cases hp : x > 0
  · rw [eq_inf_of_isInf h hp]
    decide +kernel
  · rw [eq_neg_inf_of_isInf h hp]
    decide +kernel

theorem finite_of_shortest {x : Float} {d : Decimal} (h : shortest x = some d) : finiteFloat x = true := by
  cases hf : finiteFloat x
  · unfold shortest at h
    simp [hf] at h
  · rfl

theorem shortest_none {x : Float} (h : finiteFloat x = false) : shortest x = none := by
  unfold shortest
  simp [h]

theorem toValue_float_finite {x : Float} {d : Decimal} (hs : shortest x = some d) : toValue x = .decimal d := by
  show (match shortest x with | some d => _ | none => _) = _
  rw [hs]

theorem toValue_float_special {x : Float} (hf : finiteFloat x = false) :
    toValue x = .string (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity") := by
  show (match shortest x with | some d => _ | none => _) = _
  rw [shortest_none hf]

theorem fromValue_float_iff (w : Value) (x : Float) :
    fromValue? w = .ok x ↔
      (∃ d, w = .decimal d ∧ shortest x = some d) ∨ (w = .string "NaN" ∧ x = Float.nan) ∨
        (w = .string "Infinity" ∧ x = Float.inf) ∨ (w = .string "-Infinity" ∧ x = -Float.inf) := by
  have hnan : (0.0 / 0.0 : Float) = Float.nan := FloatText.toBits_inj (by decide +kernel)
  have hinf : (1.0 / 0.0 : Float) = Float.inf := FloatText.toBits_inj (by decide +kernel)
  have hninf : (-1.0 / 0.0 : Float) = -Float.inf := FloatText.toBits_inj (by decide +kernel)
  simp only [fromValue?]
  split
  · rename_i d
    simp only [Value.decimal.injEq, exists_eq_left', reduceCtorEq, false_and, or_false]
    constructor
    · intro h
      split at h
      · rename_i y hy
        split at h
        · rename_i e he
          split at h
          · rename_i hed
            simp only [pure_eq_ok, Except.ok.injEq] at h
            subst h hed
            exact he
          · cases h
        · cases h
      · cases h
    · intro hs
      rw [floatsReadBack x (finite_of_shortest hs) d hs]
      simp only [hs]
      simp [pure_eq_ok]
  · simp [hnan, pure_eq_ok, eq_comm]
  · simp [hinf, pure_eq_ok, eq_comm]
  · simp [hninf, pure_eq_ok, eq_comm]
  · rename_i h1 h2 h3 h4
    constructor
    · intro h
      cases h
    · rintro (⟨d, h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact (h1 d h).elim
      · exact (h2 h).elim
      · exact (h3 h).elim
      · exact (h4 h).elim

theorem codec_float (x : Float) :
    (if x.isNaN then toValue x = .string "NaN"
      else if x.isInf then toValue x = .string (if x > 0 then "Infinity" else "-Infinity")
      else ∃ d : Decimal, toValue x = .decimal d ∧ d.IsShortest x) ∧
      ∀ w : Value, fromValue? w = .ok x ↔ w = toValue x := by
  have bits_ne : ∀ {a b : Float}, a.toBits ≠ b.toBits → a ≠ b := fun h e => h (congrArg Float.toBits e)
  constructor
  · by_cases hn : x.isNaN = true
    · rw [ite_eq_left hn, toValue_float_special (finiteFloat_of_isNaN hn), ite_eq_left hn]
    · rw [ite_eq_right hn]
      by_cases hi : x.isInf = true
      · rw [ite_eq_left hi, toValue_float_special (finiteFloat_of_isInf hi), ite_eq_right hn]
      · rw [ite_eq_right hi]
        have hx := finiteFloat_of_not (by simpa using hn) (by simpa using hi)
        obtain ⟨D, hs⟩ := shortest_isSome x hx
        exact ⟨D, toValue_float_finite hs, shortest_isShortest x hx D hs⟩
  · intro w
    rw [fromValue_float_iff]
    cases hs : shortest x with
    | some D =>
      have hx := finite_of_shortest hs
      rw [toValue_float_finite hs]
      constructor
      · rintro (⟨d, rfl, hd⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩)
        · cases hd
          rfl
        · exact absurd hx (by decide +kernel)
        · exact absurd hx (by decide +kernel)
        · exact absurd hx (by decide +kernel)
      · rintro rfl
        exact .inl ⟨D, rfl, rfl⟩
    | none =>
      have hf : finiteFloat x = false := by
        cases h : finiteFloat x
        · rfl
        · obtain ⟨D, hD⟩ := shortest_isSome x h
          rw [hs] at hD
          cases hD
      rw [toValue_float_special hf]
      by_cases hn : x.isNaN = true
      · have hxn := eq_nan_of_isNaN hn
        rw [ite_eq_left hn]
        constructor
        · rintro (⟨d, -, hd⟩ | ⟨h, -⟩ | ⟨-, h⟩ | ⟨-, h⟩)
          · cases hd
          · exact h
          · exact absurd (hxn.symm.trans h) (bits_ne (by decide +kernel))
          · exact absurd (hxn.symm.trans h) (bits_ne (by decide +kernel))
        · rintro rfl
          exact .inr (.inl ⟨rfl, hxn⟩)
      · rw [ite_eq_right hn]
        have hi : x.isInf = true := by
          cases h : x.isInf
          · have := finiteFloat_of_not (by simpa using hn) h
            rw [hf] at this
            cases this
          · rfl
        by_cases hp : x > 0
        · have hxi := eq_inf_of_isInf hi hp
          rw [ite_eq_left hp]
          constructor
          · rintro (⟨d, -, hd⟩ | ⟨-, h⟩ | ⟨h, -⟩ | ⟨-, h⟩)
            · cases hd
            · exact absurd (hxi.symm.trans h) (bits_ne (by decide +kernel))
            · exact h
            · exact absurd (hxi.symm.trans h) (bits_ne (by decide +kernel))
          · rintro rfl
            exact .inr (.inr (.inl ⟨rfl, hxi⟩))
        · have hxi := eq_neg_inf_of_isInf hi hp
          rw [ite_eq_right hp]
          constructor
          · rintro (⟨d, -, hd⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩)
            · cases hd
            · exact absurd (hxi.symm.trans h) (bits_ne (by decide +kernel))
            · exact absurd (hxi.symm.trans h) (bits_ne (by decide +kernel))
            · exact h
          · rintro rfl
            exact .inr (.inr (.inr ⟨rfl, hxi⟩))

theorem codec_float_rejects_null :
    ¬ ∀ (x : Float),
      (if x.isNaN then @toValue Float ⟨fun _ => .null⟩ x = .string "NaN"
        else if x.isInf then @toValue Float ⟨fun _ => .null⟩ x = .string (if x > 0 then "Infinity" else "-Infinity")
        else ∃ d : Decimal, @toValue Float ⟨fun _ => .null⟩ x = .decimal d ∧ d.IsShortest x) ∧
        ∀ w : Value, @fromValue? Float ⟨fun _ => .error ""⟩ w = .ok x ↔ w = @toValue Float ⟨fun _ => .null⟩ x := by
  intro h
  exact absurd (((h 0.0).2 .null).mpr rfl) (fun e => by cases e)

end ExactJSON
