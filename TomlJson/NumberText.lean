module

public import TomlJson.Rfc8259
public import TomlJson.Render

/-! # The text of a number is an RFC 8259 number

The renderer writes an integer as `toString` does and a float as `Decimal.toFloatText` does; these
lemmas say that every character of such a text is one that numbers are written in, that the text is
not empty, and that RFC 8259 reads an integer's text back as that integer. They also say that the
reference reader's sorting of a table's members leaves members already in key order as they are.
-/

public section

namespace TomlJson

universe u

private theorem isNumberChar_of_isDigit {c : Char} (h : c.isDigit = true) : Rfc8259.isNumberChar c = true := by
  simp only [Rfc8259.isNumberChar, h, Bool.true_or]

private theorem isDigit_toDigits {m : Nat} : ∀ c ∈ Nat.toDigits 10 m, c.isDigit = true :=
  fun _ h => Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

private theorem numberChars_toDigits (m : Nat) : ∀ c ∈ Nat.toDigits 10 m, Rfc8259.isNumberChar c = true :=
  fun c h => isNumberChar_of_isDigit (isDigit_toDigits c h)

theorem numberChars_toString (n : Int) : ∀ c ∈ (toString n).toList, Rfc8259.isNumberChar c = true := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · rw [Nat.toList_repr]
    exact numberChars_toDigits _
  · rw [String.toList_append, Nat.toList_repr]
    exact List.forall_mem_append.mpr ⟨by decide, numberChars_toDigits _⟩

theorem toString_toList_ne_nil (n : Int) : (toString n).toList ≠ [] := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · rw [Nat.toList_repr]
    exact Nat.toDigits_ne_nil
  · rw [String.toList_append]
    exact List.append_ne_nil_of_left_ne_nil (by decide) _

theorem numberChars_toFloatText (d : Decimal) : ∀ c ∈ d.toFloatText.toList, Rfc8259.isNumberChar c = true := by
  have digits := numberChars_toDigits d.digits
  have exponent := numberChars_toString (d.exponent + (Nat.toDigits 10 d.digits).length - 1)
  have zeros : ∀ n, ∀ c ∈ Decimal.zeros n, Rfc8259.isNumberChar c = true := fun n c h => by
    simp only [Decimal.zeros, List.mem_replicate] at h
    rw [h.2]
    decide
  have taken : ∀ k, ∀ c ∈ (Nat.toDigits 10 d.digits).take k, Rfc8259.isNumberChar c = true := fun _ c h =>
    digits c (List.mem_of_mem_take h)
  have dropped : ∀ k, ∀ c ∈ (Nat.toDigits 10 d.digits).drop k, Rfc8259.isNumberChar c = true := fun _ c h =>
    digits c (List.mem_of_mem_drop h)
  have sign : ∀ b : Bool, ∀ c ∈ (if b = true then ['-'] else []), Rfc8259.isNumberChar c = true := by decide
  unfold Decimal.toFloatText
  dsimp only
  split
  · rw [String.toList_ofList]
    exact List.forall_mem_append.mpr ⟨sign _, by decide⟩
  · rw [String.toList_ofList]
    refine List.forall_mem_append.mpr ⟨sign _, ?_⟩
    split
    · split
      · exact List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨digits, zeros _⟩, by decide⟩
      · split
        · exact List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨taken _, by decide⟩, dropped _⟩
        · exact List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨by decide, zeros _⟩, digits⟩
    · refine List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr
        ⟨List.forall_mem_append.mpr ⟨taken _, by decide⟩, ?_⟩, by decide⟩, exponent⟩
      split
      · decide
      · exact dropped _

theorem toFloatText_toList_ne_nil (d : Decimal) : d.toFloatText.toList ≠ [] := by
  unfold Decimal.toFloatText
  dsimp only
  split
  · rw [String.toList_ofList]
    exact List.append_ne_nil_of_right_ne_nil _ (by decide)
  · rw [String.toList_ofList]
    refine List.append_ne_nil_of_right_ne_nil _ ?_
    split
    · split
      · simp
      · split <;> simp
    · simp

private theorem span_loop_of_forall {α : Type u} {p : α → Bool} : ∀ (l acc : List α), (∀ x ∈ l, p x = true) →
    List.span.loop p l acc = (acc.reverse ++ l, [])
  | [], acc, _ => by simp [List.span.loop]
  | a :: as, acc, h => by
    simp only [List.span.loop, h a List.mem_cons_self]
    rw [span_loop_of_forall as (a :: acc) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

private theorem span_of_forall {α : Type u} {p : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = true) :
    l.span p = (l, []) := by
  unfold List.span
  rw [span_loop_of_forall l [] h]
  simp

private theorem toDigits_head?_ne_zero (m : Nat) (hm : 0 < m) : (Nat.toDigits 10 m).head? ≠ some '0' := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · simp only [List.head?_cons, ne_eq, Option.some.injEq, Nat.digitChar_eq_zero]
      omega
    · rw [List.head?_append]
      have high := ih (m / 10) (by omega) (by omega)
      cases h : (Nat.toDigits 10 (m / 10)).head? with
      | none => simp at h
      | some c =>
        simp only [h] at high ⊢
        exact high

private theorem toDigits_leading (m : Nat) :
    ¬((Nat.toDigits 10 m).head? = some '0' ∧ (Nat.toDigits 10 m).length > 1) := by
  rintro ⟨head, long⟩
  cases m with
  | zero => simp at long
  | succ m => exact toDigits_head?_ne_zero (m + 1) (by omega) head

private theorem numberValue_digits (negative : Bool) {ds : List Char} (digits : ∀ c ∈ ds, c.isDigit = true)
    (nonempty : ds ≠ []) (leading : ¬(ds.head? = some '0' ∧ ds.length > 1)) :
    Rfc8259.numberValue (if negative then '-' :: ds else ds) =
      .ok (.integer (if negative then -(Nat.ofDigitChars 10 ds 0 : Int) else Nat.ofDigitChars 10 ds 0)) := by
  obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  have hc : c ≠ '-' := fun h => absurd (h ▸ digits c List.mem_cons_self) (by decide)
  unfold Rfc8259.numberValue
  split
  rename_i signed t sign
  have unsigned : signed = negative ∧ t = c :: cs := by
    cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte] at sign <;> (try split at sign) <;> simp_all
  obtain ⟨rfl, rfl⟩ := unsigned
  rw [span_of_forall digits]
  dsimp only
  rw [ite_eq_right (by simp), ite_eq_right (by simpa using leading)]
  simp [Rfc8259.digitsValue]

theorem numberValue_toString (n : Int) : Rfc8259.numberValue (toString n).toList = .ok (.integer n) := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · rename_i h
    rw [Nat.toList_repr]
    have read := numberValue_digits false isDigit_toDigits Nat.toDigits_ne_nil (toDigits_leading n.toNat)
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.ofDigitChars_ten_toDigits] at read
    rw [read, Int.toNat_of_nonneg h]
  · rename_i h
    rw [String.toList_append, Nat.toList_repr]
    have read := numberValue_digits true isDigit_toDigits Nat.toDigits_ne_nil (toDigits_leading (-n).toNat)
    simp only [↓reduceIte, Nat.ofDigitChars_ten_toDigits] at read
    rw [show "-".toList = ['-'] from rfl, List.singleton_append, read, Int.toNat_of_nonneg (by omega), Int.neg_neg]

private theorem lt_of_keysIncreaseFrom : ∀ {p : String} {ks : List String}, keysIncreaseFrom p ks = true →
    ∀ k ∈ ks, p < k
  | _, [], _ => by simp
  | _, _ :: _, h => by
    simp only [keysIncreaseFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact h.1
    · exact Std.lt_trans h.1 (lt_of_keysIncreaseFrom h.2 k hk)

private theorem pairwise_of_keysIncreaseFrom : ∀ {p : String} {ks : List String}, keysIncreaseFrom p ks = true →
    ks.Pairwise (· < ·)
  | _, [], _ => List.Pairwise.nil
  | _, _ :: _, h => by
    simp only [keysIncreaseFrom, Bool.and_eq_true] at h
    exact List.Pairwise.cons (lt_of_keysIncreaseFrom h.2) (pairwise_of_keysIncreaseFrom h.2)

private theorem pairwise_of_keysIncrease : ∀ {ks : List String}, keysIncrease ks = true → ks.Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | _ :: _, h => List.Pairwise.cons (lt_of_keysIncreaseFrom h) (pairwise_of_keysIncreaseFrom h)

theorem mergeSort_of_keysIncrease (l : List (String × Value)) (h : keysIncrease (l.map (·.1)) = true) :
    l.mergeSort (fun a b => decide (a.1 ≤ b.1)) = l :=
  List.mergeSort_of_pairwise ((List.pairwise_map.mp (pairwise_of_keysIncrease h)).imp fun lt =>
    decide_eq_true (Std.le_of_lt lt))

private theorem neighboursDistinct_of_pairwise : ∀ {l : List (String × Value)},
    l.Pairwise (fun a b => a.1 < b.1) → Rfc8259.neighboursDistinct l = true
  | [], _ => rfl
  | [_], _ => rfl
  | _ :: _ :: _, h => by
    simp only [Rfc8259.neighboursDistinct, Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨Std.ne_of_lt (List.rel_of_pairwise_cons h List.mem_cons_self), neighboursDistinct_of_pairwise h.of_cons⟩

theorem neighboursDistinct_of_keysIncrease (l : List (String × Value)) (h : keysIncrease (l.map (·.1)) = true) :
    Rfc8259.neighboursDistinct l = true :=
  neighboursDistinct_of_pairwise (List.pairwise_map.mp (pairwise_of_keysIncrease h))

end TomlJson
