module

public import ExactJSON.Text

@[expose] public section

namespace ExactJSON

theorem pushChar_escapeChar (c : Char) : (pushChar "" c).toList = (escapeChar c).toList := by
  by_cases h1 : c = '"'
  · subst h1; simp [pushChar, escapeChar]
  by_cases h2 : c = '\\'
  · subst h2; simp [pushChar, escapeChar]
  by_cases h3 : mustEscape c = true
  · simp only [pushChar, escapeChar, beq_iff_eq, h1, h2, h3, Bool.not_true, Bool.false_eq_true, ite_false,
      ite_true]
    by_cases b : c = '\x08'
    · simp [b]
    by_cases t : c = '\t'
    · simp [t]
    by_cases nl : c = '\n'
    · simp [nl]
    by_cases f : c = '\x0c'
    · simp [f]
    by_cases r : c = '\r'
    · simp [r]
    simp only [b, t, nl, f, r, ite_false, String.toList_push, String.toList_append]
    simp [hexDigit, hexChar]
  · have hb : c ≠ '\x08' ∧ c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '\x0c' ∧ c ≠ '\r' := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro h; subst h; simp [mustEscape] at h3)
    simp only [Bool.not_eq_true] at h3
    simp only [pushChar, escapeChar, beq_iff_eq, h1, h2, h3, hb.1, hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2,
      Bool.not_false, Bool.false_eq_true, ite_false, ite_true]
    simp

theorem escapeList_eq (cs : List Char) : escapeList cs = (String.join (cs.map escapeChar)).toList := by
  induction cs with
  | nil => simp [escapeList]
  | cons c cs ih =>
    rw [escapeList_cons, pushChar_escapeChar, ih]
    simp [String.join_cons, String.toList_append]

theorem stringText_toList (s : String) : (stringText s).toList = '"' :: (escapeList s.toList ++ ['"']) := by
  simp [stringText, String.toList_append, escapeList_eq]

namespace Value

mutual

theorem render_write : (v : Value) → (render v).toList = (write v).toList
  | .null => by rw [text_null]; rfl
  | .boolean b => by cases b <;> rw [text_boolean] <;> rfl
  | .integer n => by simp [write, render, renderTo, intText_eq]
  | .decimal d => by simp [write, render, renderTo]
  | .string s => by rw [text_string]; simp [write, stringText_toList]
  | .array ⟨items⟩ => by
    rw [text_array, items_write items]
    simp [write, String.toList_append]
  | .table ⟨members⟩ => by
    rw [text_table, members_write members]
    simp [write, String.toList_append]

theorem items_write : (items : List Value) →
    itemsText items = (writeItems items).toList
  | [] => by simp [itemsText, renderItems, writeItems]
  | [v] => by rw [itemsText_singleton, render_write v]; simp [writeItems]
  | v :: w :: rest => by
    rw [itemsText_cons, render_write v, items_write (w :: rest)]
    simp [writeItems, String.toList_append]

theorem members_write : (members : List (String × Value)) →
    membersText members = (writeMembers members).toList
  | [] => by simp [membersText, renderMembers, writeMembers]
  | [(k, v)] => by
    rw [membersText_singleton]
    simp [memberText, writeMembers, String.toList_append, stringText_toList, render_write v]
  | (k, v) :: m :: rest => by
    rw [membersText_cons, members_write (m :: rest)]
    simp [memberText, writeMembers, String.toList_append, stringText_toList, render_write v]

end

theorem render_eq_write (v : Value) : render v = write v :=
  String.toList_inj.mp (render_write v)

end Value

end ExactJSON
