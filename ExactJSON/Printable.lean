module

public import ExactJSON.Render

public section

namespace ExactJSON

abbrev CleanChar (c : Char) : Prop :=
  0x20 ≤ c.toNat ∧ ¬(0x7F ≤ c.toNat ∧ c.toNat ≤ 0x9F) ∧ c.toNat ≠ 0x2028 ∧ c.toNat ≠ 0x2029

abbrev Printable (cs : List Char) : Prop := ∀ c ∈ cs, CleanChar c

theorem cleanChar_of_mustEscape {c : Char} (h : mustEscape c = false) : CleanChar c := by
  simp only [mustEscape, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne,
    ne_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨by omega, ?_, h3, h4⟩
  rintro ⟨a, b⟩
  rcases h2 with h2 | h2 <;> omega

theorem printable_append {a b : List Char} (ha : Printable a) (hb : Printable b) : Printable (a ++ b) :=
  List.forall_mem_append.mpr ⟨ha, hb⟩

theorem printable_string_append {s t : String} (hs : Printable s.toList) (ht : Printable t.toList) :
    Printable (s ++ t).toList := by
  rw [String.toList_append]
  exact printable_append hs ht

theorem printable_push {s : String} {c : Char} (hs : Printable s.toList) (hc : CleanChar c) :
    Printable (s.push c).toList := by
  rw [String.toList_push]
  refine printable_append hs fun x hx => ?_
  rw [List.mem_singleton] at hx
  subst hx
  exact hc

theorem printable_of_isDigit {c : Char} (h : c.isDigit = true) : CleanChar c := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have low := UInt32.le_iff_toNat_le.mp h.1
  have high := UInt32.le_iff_toNat_le.mp h.2
  have l : 0x30 ≤ c.toNat := Nat.le_trans (by decide) low
  have u : c.toNat ≤ 0x39 := Nat.le_trans high (by decide)
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem printable_toDigits (n : Nat) : Printable (Nat.toDigits 10 n) := fun _ h =>
  printable_of_isDigit (Nat.isDigit_of_mem_toDigits (by decide) (by decide) h)

theorem printable_natRepr (n : Nat) : Printable n.repr.toList := by
  rw [Nat.toList_repr]
  exact printable_toDigits n

theorem printable_intToString (n : Int) : Printable (toString n).toList := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · exact printable_natRepr _
  · exact printable_string_append (by decide) (printable_natRepr _)

theorem printable_hexDigit : ∀ n, n < 16 → CleanChar (hexDigit n) := by decide

theorem printable_pushChar {out : String} (c : Char) (h : Printable out.toList) :
    Printable (pushChar out c).toList := by
  unfold pushChar
  split
  · exact printable_string_append h (by decide)
  split
  · exact printable_string_append h (by decide)
  split
  · rename_i raw
    exact printable_push h (cleanChar_of_mustEscape (by simpa using raw))
  split
  · exact printable_string_append h (by decide)
  split
  · exact printable_string_append h (by decide)
  split
  · exact printable_string_append h (by decide)
  split
  · exact printable_string_append h (by decide)
  split
  · exact printable_string_append h (by decide)
  · refine printable_push (printable_push (printable_push (printable_push (printable_string_append h (by decide))
      ?_) ?_) ?_) ?_ <;> exact printable_hexDigit _ (Nat.mod_lt _ (by decide))

theorem printable_foldl_pushChar : ∀ (cs : List Char) {out : String}, Printable out.toList →
    Printable (cs.foldl pushChar out).toList
  | [], _, h => h
  | c :: rest, _, h => printable_foldl_pushChar rest (printable_pushChar c h)

theorem printable_pushString {out : String} (s : String) (h : Printable out.toList) :
    Printable (pushString out s).toList := by
  unfold pushString
  rw [String.foldl_eq_foldl_toList]
  exact printable_push (printable_foldl_pushChar _ (printable_push h (by decide))) (by decide)

theorem printable_decimalText (d : Decimal) : Printable d.text.toList := by
  have digits := printable_toDigits d.digits
  have exponent := printable_intToString (d.exponent + (Nat.toDigits 10 d.digits).length - 1)
  have zeros : ∀ n, Printable (Decimal.zeros n) := fun n c h => by
    simp only [Decimal.zeros, List.mem_replicate] at h
    rw [h.2]
    decide
  have taken : ∀ k, Printable ((Nat.toDigits 10 d.digits).take k) := fun _ c h =>
    digits c (List.mem_of_mem_take h)
  have dropped : ∀ k, Printable ((Nat.toDigits 10 d.digits).drop k) := fun _ c h =>
    digits c (List.mem_of_mem_drop h)
  have sign : ∀ b : Bool, Printable (if b = true then ['-'] else []) := by decide
  unfold Decimal.text
  dsimp only
  split
  · rw [String.toList_ofList]
    exact printable_append (sign _) (by decide)
  · rw [String.toList_ofList]
    refine printable_append (sign _) ?_
    split
    · split
      · refine printable_append (printable_append digits (zeros _)) ?_
        decide
      · split
        · refine printable_append (printable_append (taken _) ?_) (dropped _)
          decide
        · refine printable_append (printable_append ?_ (zeros _)) digits
          decide
    · refine printable_append (printable_append (printable_append (printable_append (taken _) ?_) ?_) ?_) exponent
      · decide
      · split
        · decide
        · exact dropped _
      · decide

mutual

theorem printable_renderTo {out : String} (h : Printable out.toList) :
    (v : Value) → Printable (Value.renderTo out v).toList
  | .null => printable_string_append h (by decide)
  | .string s => printable_pushString s h
  | .integer n => printable_string_append h (printable_intToString n)
  | .decimal d => printable_string_append h (printable_decimalText d)
  | .boolean b => printable_string_append h (by cases b <;> decide)
  | .array ⟨items⟩ => printable_push (printable_renderItems (printable_push h (by decide)) items) (by decide)
  | .table ⟨members⟩ =>
    printable_push (printable_renderMembers (printable_push h (by decide)) members) (by decide)

theorem printable_renderItems {out : String} (h : Printable out.toList) :
    (items : List Value) → Printable (Value.renderItems out items).toList
  | [] => h
  | [v] => printable_renderTo h v
  | v :: w :: rest => printable_renderItems (printable_push (printable_renderTo h v) (by decide)) (w :: rest)

theorem printable_renderMembers {out : String} (h : Printable out.toList) :
    (members : List (String × Value)) → Printable (Value.renderMembers out members).toList
  | [] => h
  | [(k, v)] => printable_renderTo (printable_push (printable_pushString k h) (by decide)) v
  | (k, v) :: m :: rest =>
    printable_renderMembers
      (printable_push (printable_renderTo (printable_push (printable_pushString k h) (by decide)) v) (by decide))
      (m :: rest)

end

theorem printable_render (v : Value) : Printable v.render.toList :=
  printable_renderTo (by decide) v

end ExactJSON
