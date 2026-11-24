module

public import ExactJSON.Render

/-! # A text holds no control character

Every character `Value.render` writes is at U+0020 or above: each piece it appends is a literal,
a digit, an escape or a character at U+0020 or above, since JSON's escaping writes the control
characters below U+0020 as escapes. So a text is one line, for line feeds and carriage returns
alike. -/

public section

namespace ExactJSON

/-- Every character is at U+0020 or above. -/
abbrev Printable (cs : List Char) : Prop := ∀ c ∈ cs, 0x20 ≤ c.toNat

theorem printable_append {a b : List Char} (ha : Printable a) (hb : Printable b) : Printable (a ++ b) :=
  List.forall_mem_append.mpr ⟨ha, hb⟩

theorem printable_string_append {s t : String} (hs : Printable s.toList) (ht : Printable t.toList) :
    Printable (s ++ t).toList := by
  rw [String.toList_append]
  exact printable_append hs ht

theorem printable_push {s : String} {c : Char} (hs : Printable s.toList) (hc : 0x20 ≤ c.toNat) :
    Printable (s.push c).toList := by
  rw [String.toList_push]
  refine printable_append hs fun x hx => ?_
  rw [List.mem_singleton] at hx
  subst hx
  exact hc

theorem printable_of_isDigit {c : Char} (h : c.isDigit = true) : 0x20 ≤ c.toNat := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  have low := UInt32.le_iff_toNat_le.mp h.1
  exact Nat.le_trans (by decide) low

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

theorem printable_hexDigit : ∀ n, n < 16 → 0x20 ≤ (hexDigit n).toNat := by decide

theorem printable_pushChar {out : String} (c : Char) (h : Printable out.toList) :
    Printable (pushChar out c).toList := by
  unfold pushChar
  split
  · exact printable_string_append h (by decide)
  split
  · exact printable_string_append h (by decide)
  split
  · rename_i above
    exact printable_push h (UInt32.le_iff_toNat_le.mp above)
  rename_i below
  have small : c.toNat < 0x20 := by
    have := UInt32.lt_iff_toNat_lt.mp (UInt32.not_le.mp below)
    exact this
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
  · refine printable_push (printable_push (printable_string_append h (by decide)) ?_) ?_
    · exact printable_hexDigit _ (by omega)
    · exact printable_hexDigit _ (Nat.mod_lt _ (by decide))

theorem printable_foldl_pushChar : ∀ (cs : List Char) {out : String}, Printable out.toList →
    Printable (cs.foldl pushChar out).toList
  | [], _, h => h
  | c :: rest, _, h => printable_foldl_pushChar rest (printable_pushChar c h)

theorem printable_pushString {out : String} (s : String) (h : Printable out.toList) :
    Printable (pushString out s).toList := by
  unfold pushString
  rw [String.foldl_eq_foldl_toList]
  exact printable_push (printable_foldl_pushChar _ (printable_push h (by decide))) (by decide)

theorem printable_toFloatText (d : Decimal) : Printable d.toFloatText.toList := by
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
  unfold Decimal.toFloatText
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

theorem printable_floatText (x : Float) : Printable (floatText x).toList := by
  unfold floatText
  split
  · rename_i text found
    unfold Float.toCanonical? at found
    cases shortest : FloatText.shortest x with
    | none => simp [shortest] at found
    | some d =>
      simp only [shortest, Option.map_some, Option.some.injEq] at found
      subst found
      exact printable_toFloatText d
  · split
    · decide
    · split <;> decide

mutual

theorem printable_renderTo {out : String} (h : Printable out.toList) :
    (v : Value) → Printable (Value.renderTo out v).toList
  | .null => printable_string_append h (by decide)
  | .string s => printable_pushString s h
  | .integer n => printable_string_append h (printable_intToString n)
  | .float x => printable_string_append h (printable_floatText x)
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
