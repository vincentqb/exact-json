module

public import ExactJSON.OfScientific

public section

namespace ExactJSON

namespace RenderInjective

def NumberToken (v : Value) : Prop :=
  (∀ c ∈ (Value.render v).toList, Rfc8259.isNumberChar c = true) ∧ (Value.render v).toList ≠ [] ∧
    Rfc8259.numberValue (Value.render v).toList = .ok v

theorem numberToken_integer (n : Int) : NumberToken (.integer n) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [render_integer_toList]
  · exact numberChars_toString n
  · exact toString_toList_ne_nil n
  · exact numberValue_toString n

theorem numberToken_float (x : Float) (hx : finiteFloat x = true) : NumberToken (.float x) := by
  have hre := floatsReadBack ofScientificRounds x hx
  obtain ⟨d, hd⟩ := float_reread_text hre
  refine ⟨?_, ?_, ?_⟩ <;> rw [render_float_toList]
  · rw [hd]; exact numberChars_toFloatText d
  · rw [hd]; exact toFloatText_toList_ne_nil d
  · exact rereadFloat_numberValue hre

theorem numberToken_head {w : Value} (hw : NumberToken w) :
    ∃ c t, (Value.render w).toList = c :: t ∧ Rfc8259.isNumberChar c = true := by
  obtain ⟨hc, hne, -⟩ := hw
  obtain ⟨c, t, h⟩ := List.exists_cons_of_ne_nil hne
  exact ⟨c, t, h, hc c (by rw [h]; simp)⟩

theorem valid_head (w : Value) (hw : w.isValid = true) : ∃ c t, (Value.render w).toList = c :: t ∧
    (c = 'n' → w = .null) ∧ (c = 't' → w = .boolean true) ∧ (c = 'f' → w = .boolean false) ∧
    (c = '"' → ∃ s, w = .string s) ∧ (c = '[' → ∃ items, w = .array ⟨items⟩) ∧
    (c = '{' → ∃ members, w = .table ⟨members⟩) ∧ (Rfc8259.isNumberChar c = true → NumberToken w) ∧
    c ≠ 'N' ∧ c ≠ 'I' := by
  have number : ∀ w : Value, NumberToken w → ∃ c t, (Value.render w).toList = c :: t ∧
      (c = 'n' → w = .null) ∧ (c = 't' → w = .boolean true) ∧ (c = 'f' → w = .boolean false) ∧
      (c = '"' → ∃ s, w = .string s) ∧ (c = '[' → ∃ items, w = .array ⟨items⟩) ∧
      (c = '{' → ∃ members, w = .table ⟨members⟩) ∧ (Rfc8259.isNumberChar c = true → NumberToken w) ∧
      c ≠ 'N' ∧ c ≠ 'I' := by
    intro w hw
    obtain ⟨c, t, h, hc⟩ := numberToken_head hw
    refine ⟨c, t, h, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => hw, ?_, ?_⟩ <;>
      (intro he; subst he; exact absurd hc (by decide))
  cases w with
  | null =>
    refine ⟨'n', _, Value.text_null, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | (intro he; exact absurd he (by decide)) | decide
  | boolean b =>
    cases b
    · refine ⟨'f', _, Value.text_boolean false, ?_, ?_, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | (intro he; exact absurd he (by decide)) | decide
    · refine ⟨'t', _, Value.text_boolean true, ?_, fun _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        first | (intro he; exact absurd he (by decide)) | decide
  | string s =>
    refine ⟨'"', _, Value.text_string s, ?_, ?_, ?_, fun _ => ⟨s, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first | (intro he; exact absurd he (by decide)) | decide
  | array a =>
    cases a with
    | mk items =>
      refine ⟨'[', _, Value.text_array items, ?_, ?_, ?_, ?_, fun _ => ⟨items, rfl⟩, ?_, ?_, ?_, ?_⟩ <;>
        first | (intro he; exact absurd he (by decide)) | decide
  | table a =>
    cases a with
    | mk members =>
      refine ⟨'{', _, Value.text_table members, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨members, rfl⟩, ?_, ?_, ?_⟩ <;>
        first | (intro he; exact absurd he (by decide)) | decide
  | integer n => exact number _ (numberToken_integer n)
  | float x => exact number _ (numberToken_float x hw)

theorem head_eq {a b r1 r2 t u : List Char} {c d : Char} (ha : a = c :: t) (hb : b = d :: u)
    (E : a ++ r1 = b ++ r2) : c = d := by
  subst ha hb
  simp only [List.cons_append, List.cons.injEq] at E
  exact E.1

def Stop (r : List Char) : Prop := ∀ c t, r = c :: t → c = ',' ∨ c = ']' ∨ c = '}'

theorem stop_nil : Stop [] := fun _ _ h => by cases h

theorem stop_cons (c : Char) (t : List Char) (h : c = ',' ∨ c = ']' ∨ c = '}') : Stop (c :: t) :=
  fun _ _ he => by cases he; exact h

theorem Stop.noNumber {r : List Char} (h : Stop r) : ∀ c t, r = c :: t → Rfc8259.isNumberChar c = false :=
  fun c t he => by rcases h c t he with rfl | rfl | rfl <;> rfl

theorem span_token (text rest : List Char) (htext : ∀ c ∈ text, Rfc8259.isNumberChar c = true) (hrest : Stop rest) :
    (text ++ rest).span Rfc8259.isNumberChar = (text, rest) := by
  have := span_loop_text Rfc8259.isNumberChar text rest [] htext hrest.noNumber
  simpa [List.span] using this

theorem numberToken_inj {v w : Value} {r1 r2 : List Char} (hv : NumberToken v) (hw : NumberToken w)
    (h1 : Stop r1) (h2 : Stop r2)
    (E : (Value.render v).toList ++ r1 = (Value.render w).toList ++ r2) : v = w := by
  have s1 := span_token _ _ hv.1 h1
  have s2 := span_token _ _ hw.1 h2
  rw [E, s2] at s1
  simp only [Prod.mk.injEq] at s1
  have := hv.2.2
  rw [← s1.1, hw.2.2] at this
  cases this
  rfl

theorem restOk_not_I {r : List Char} (h : Stop r) (t : List Char) : r ≠ 'I' :: t := fun he => by
  rcases h 'I' t he with h | h | h <;> exact absurd h (by decide)

theorem nonfinite_text (x : Float) (hx : finiteFloat x = false) :
    (Value.render (.float x)).toList = "NaN".toList ∨ (Value.render (.float x)).toList = "Infinity".toList ∨
      (Value.render (.float x)).toList = "-Infinity".toList := by
  rw [render_float_toList]
  have h : floatText x = if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity" := by
    simp [floatText, Float.toCanonical?, FloatText.shortest, hx]
  rw [h]
  split
  · exact .inl rfl
  · split
    · exact .inr (.inl rfl)
    · exact .inr (.inr rfl)

theorem nonfinite_ne {x : Float} (hx : finiteFloat x = false) {w : Value} (hw : w.isValid = true)
    {r1 r2 : List Char} (h2 : Stop r2)
    (E : (Value.render (.float x)).toList ++ r1 = (Value.render w).toList ++ r2) : False := by
  obtain ⟨c, t, hc, -, -, -, -, -, -, hnum, hN, hI⟩ := valid_head w hw
  rcases nonfinite_text x hx with h | h | h
  · rw [h] at E
    exact hN (head_eq rfl hc E).symm
  · rw [h] at E
    exact hI (head_eq rfl hc E).symm
  · rw [h, show "-Infinity".toList = ['-', 'I', 'n', 'f', 'i', 'n', 'i', 't', 'y'] from rfl] at E
    have hm : c = '-' := (head_eq rfl hc E).symm
    subst hm
    have hw' := hnum (by decide)
    rw [hc] at E
    simp only [List.cons_append, List.cons.injEq, true_and] at E
    cases t with
    | nil =>
      simp only [List.nil_append] at E
      exact restOk_not_I h2 _ E.symm
    | cons c2 t2 =>
      have hc2 := hw'.1 c2 (by rw [hc]; simp)
      simp only [List.cons_append, List.cons.injEq] at E
      rw [← E.1] at hc2
      exact absurd hc2 (by decide)

theorem chars_inj {a b r1 r2 : List Char} (E : escapeList a ++ '"' :: r1 = escapeList b ++ '"' :: r2) :
    a = b ∧ r1 = r2 := by
  have h := congrArg (fun l => Rfc8259.chars l []) E
  simp only [spec_chars_escape, List.reverse_nil, List.nil_append, Except.ok.injEq, Prod.mk.injEq] at h
  exact h

theorem memberText_inj {k k' : String} {v v' : Value} {s1 s2 : List Char}
    (E : Value.memberText k v ++ s1 = Value.memberText k' v' ++ s2) :
    k = k' ∧ (Value.render v).toList ++ s1 = (Value.render v').toList ++ s2 := by
  unfold Value.memberText at E
  simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at E
  obtain ⟨hk, hr⟩ := chars_inj E
  simp only [List.cons.injEq, true_and] at hr
  exact ⟨String.toList_inj.mp hk, hr⟩

mutual

theorem inj_value : (v : Value) → ∀ (w : Value) (r1 r2 : List Char), Stop r1 → Stop r2 →
    w.isValid = true → (Value.render v).toList ++ r1 = (Value.render w).toList ++ r2 → v = w
  | .null, w, r1, r2, _, _, hw, E => by
    obtain ⟨c, t, hc, hn, -⟩ := valid_head w hw
    exact (hn (head_eq Value.text_null hc E).symm).symm
  | .boolean b, w, r1, r2, _, _, hw, E => by
    obtain ⟨c, t, hc, -, ht, hf, -⟩ := valid_head w hw
    cases b
    · exact (hf (head_eq (Value.text_boolean false) hc E).symm).symm
    · exact (ht (head_eq (Value.text_boolean true) hc E).symm).symm
  | .string s, w, r1, r2, _, _, hw, E => by
    obtain ⟨c, t, hc, -, -, -, hs, -⟩ := valid_head w hw
    obtain ⟨s', rfl⟩ := hs (head_eq (Value.text_string s) hc E).symm
    rw [Value.text_string, Value.text_string] at E
    simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at E
    rw [String.toList_inj.mp (chars_inj E).1]
  | .integer n, w, r1, r2, h1, h2, hw, E => by
    obtain ⟨c, t, hc, -, -, -, -, -, -, hnum, -⟩ := valid_head w hw
    obtain ⟨c', t', hc', hcn⟩ := numberToken_head (numberToken_integer n)
    have he := head_eq hc' hc E
    subst he
    exact numberToken_inj (numberToken_integer n) (hnum hcn) h1 h2 E
  | .float x, w, r1, r2, h1, h2, hw, E => by
    cases hx : finiteFloat x
    · exact (nonfinite_ne hx hw h2 E).elim
    · obtain ⟨c, t, hc, -, -, -, -, -, -, hnum, -⟩ := valid_head w hw
      obtain ⟨c', t', hc', hcn⟩ := numberToken_head (numberToken_float x hx)
      have he := head_eq hc' hc E
      subst he
      exact numberToken_inj (numberToken_float x hx) (hnum hcn) h1 h2 E
  | .array ⟨items⟩, w, r1, r2, _, _, hw, E => by
    obtain ⟨c, t, hc, -, -, -, -, ha, -⟩ := valid_head w hw
    obtain ⟨items', rfl⟩ := ha (head_eq (Value.text_array items) hc E).symm
    rw [Value.text_array, Value.text_array] at E
    simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at E
    have hv : itemsValid items' = true := by
      rw [Rfc8259.spec_isValid_array] at hw
      exact hw
    rw [inj_items items items' r1 r2 hv E]
  | .table ⟨members⟩, w, r1, r2, _, _, hw, E => by
    obtain ⟨c, t, hc, -, -, -, -, -, ht, -⟩ := valid_head w hw
    obtain ⟨members', rfl⟩ := ht (head_eq (Value.text_table members) hc E).symm
    rw [Value.text_table, Value.text_table] at E
    simp only [List.cons_append, List.append_assoc, List.cons.injEq, true_and] at E
    have hv : membersValid members' = true := by
      rw [Rfc8259.spec_isValid_table] at hw
      simp only [Bool.and_eq_true] at hw
      exact hw.2
    rw [inj_members members members' r1 r2 hv E]

theorem inj_items : (items : List Value) → ∀ (items' : List Value) (r1 r2 : List Char),
    itemsValid items' = true → Value.itemsText items ++ ']' :: r1 = Value.itemsText items' ++ ']' :: r2 →
    items = items'
  | [], items', r1, r2, _, E => by
    cases items' with
    | nil => rfl
    | cons v' vs' =>
      obtain ⟨c, t, hc, -, hb, -⟩ := itemsText_head v' vs'
      exact absurd (head_eq (a := [']']) (t := []) rfl hc (by simpa [Value.itemsText, Value.renderItems] using E)).symm hb
  | [v], items', r1, r2, hw, E => by
    cases items' with
    | nil =>
      obtain ⟨c, t, hc, -, hb, -⟩ := itemsText_head v []
      exact absurd (head_eq (b := [']']) (u := []) hc rfl (by simpa [Value.itemsText, Value.renderItems] using E)) hb
    | cons v' vs' =>
      simp only [itemsValid, Bool.and_eq_true] at hw
      cases vs' with
      | nil =>
        rw [Value.itemsText_singleton, Value.itemsText_singleton] at E
        rw [inj_value v v' (']' :: r1) (']' :: r2) (stop_cons _ _ (by simp)) (stop_cons _ _ (by simp))
          hw.1 E]
      | cons w' ws' =>
        rw [Value.itemsText_singleton, Value.itemsText_cons] at E
        simp only [List.append_assoc, List.cons_append] at E
        have he := inj_value v v' (']' :: r1) (',' :: (Value.itemsText (w' :: ws') ++ ']' :: r2))
          (stop_cons _ _ (by simp)) (stop_cons _ _ (by simp)) hw.1 E
        subst he
        simp only [List.append_cancel_left_eq, List.cons.injEq] at E
        exact absurd E.1 (by decide)
  | v :: w :: rest, items', r1, r2, hw, E => by
    cases items' with
    | nil =>
      obtain ⟨c, t, hc, -, hb, -⟩ := itemsText_head v (w :: rest)
      exact absurd (head_eq (b := [']']) (u := []) hc rfl (by simpa [Value.itemsText, Value.renderItems] using E)) hb
    | cons v' vs' =>
      simp only [itemsValid, Bool.and_eq_true] at hw
      cases vs' with
      | nil =>
        rw [Value.itemsText_cons, Value.itemsText_singleton] at E
        simp only [List.append_assoc, List.cons_append] at E
        have he := inj_value v v' (',' :: (Value.itemsText (w :: rest) ++ ']' :: r1)) (']' :: r2)
          (stop_cons _ _ (by simp)) (stop_cons _ _ (by simp)) hw.1 E
        subst he
        simp only [List.append_cancel_left_eq, List.cons.injEq] at E
        exact absurd E.1 (by decide)
      | cons w' ws' =>
        rw [Value.itemsText_cons, Value.itemsText_cons] at E
        simp only [List.append_assoc, List.cons_append] at E
        have he := inj_value v v' (',' :: (Value.itemsText (w :: rest) ++ ']' :: r1))
          (',' :: (Value.itemsText (w' :: ws') ++ ']' :: r2))
          (stop_cons _ _ (by simp)) (stop_cons _ _ (by simp)) hw.1 E
        subst he
        simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at E
        rw [inj_items (w :: rest) (w' :: ws') r1 r2 hw.2 E]

theorem inj_members : (members : List (String × Value)) → ∀ (members' : List (String × Value)) (r1 r2 : List Char),
    membersValid members' = true →
    Value.membersText members ++ '}' :: r1 = Value.membersText members' ++ '}' :: r2 → members = members'
  | [], members', r1, r2, _, E => by
    cases members' with
    | nil => rfl
    | cons m ms =>
      obtain ⟨k, v⟩ := m
      obtain ⟨t, ht⟩ := membersText_head k v ms
      exact absurd (head_eq (a := ['}']) (t := []) rfl ht (by simpa [Value.membersText, Value.renderMembers] using E))
        (by decide)
  | [(k, v)], members', r1, r2, hw, E => by
    cases members' with
    | nil =>
      obtain ⟨t, ht⟩ := membersText_head k v []
      exact absurd (head_eq (b := ['}']) (u := []) ht rfl (by simpa [Value.membersText, Value.renderMembers] using E))
        (by decide)
    | cons m ms =>
      obtain ⟨k', v'⟩ := m
      simp only [membersValid, Bool.and_eq_true] at hw
      cases ms with
      | nil =>
        rw [Value.membersText_singleton, Value.membersText_singleton] at E
        obtain ⟨hk, E'⟩ := memberText_inj E
        subst hk
        rw [inj_value v v' ('}' :: r1) ('}' :: r2) (stop_cons _ _ (by simp)) (stop_cons _ _ (by simp))
          hw.1 E']
      | cons m2 ms2 =>
        rw [Value.membersText_singleton, Value.membersText_cons] at E
        simp only [List.append_assoc, List.cons_append] at E
        obtain ⟨hk, E'⟩ := memberText_inj E
        subst hk
        have he := inj_value v v' ('}' :: r1) (',' :: (Value.membersText (m2 :: ms2) ++ '}' :: r2))
          (stop_cons _ _ (by simp)) (stop_cons _ _ (by simp)) hw.1 E'
        subst he
        simp only [List.append_cancel_left_eq, List.cons.injEq] at E'
        exact absurd E'.1 (by decide)
  | (k, v) :: m :: rest, members', r1, r2, hw, E => by
    cases members' with
    | nil =>
      obtain ⟨t, ht⟩ := membersText_head k v (m :: rest)
      exact absurd (head_eq (b := ['}']) (u := []) ht rfl (by simpa [Value.membersText, Value.renderMembers] using E))
        (by decide)
    | cons m' ms =>
      obtain ⟨k', v'⟩ := m'
      simp only [membersValid, Bool.and_eq_true] at hw
      cases ms with
      | nil =>
        rw [Value.membersText_cons, Value.membersText_singleton] at E
        simp only [List.append_assoc, List.cons_append] at E
        obtain ⟨hk, E'⟩ := memberText_inj E
        subst hk
        have he := inj_value v v' (',' :: (Value.membersText (m :: rest) ++ '}' :: r1)) ('}' :: r2)
          (stop_cons _ _ (by simp)) (stop_cons _ _ (by simp)) hw.1 E'
        subst he
        simp only [List.append_cancel_left_eq, List.cons.injEq] at E'
        exact absurd E'.1 (by decide)
      | cons m2 ms2 =>
        rw [Value.membersText_cons, Value.membersText_cons] at E
        simp only [List.append_assoc, List.cons_append] at E
        obtain ⟨hk, E'⟩ := memberText_inj E
        subst hk
        have he := inj_value v v' (',' :: (Value.membersText (m :: rest) ++ '}' :: r1))
          (',' :: (Value.membersText (m2 :: ms2) ++ '}' :: r2))
          (stop_cons _ _ (by simp)) (stop_cons _ _ (by simp)) hw.1 E'
        subst he
        simp only [List.append_cancel_left_eq, List.cons.injEq, true_and] at E'
        rw [inj_members (m :: rest) (m2 :: ms2) r1 r2 hw.2 E']

end

end RenderInjective

theorem render_injective_valid (v w : Value) (hw : w.Valid) (h : v.render = w.render) : v = w :=
  RenderInjective.inj_value v w [] [] RenderInjective.stop_nil RenderInjective.stop_nil hw (by rw [h])

theorem parse_render_invalid_of (v : Value) (h : ¬ v.Valid) : (Value.parse v.render).toOption = none := by
  cases hp : Value.parse v.render with
  | error e => rfl
  | ok w =>
    exfalso
    obtain ⟨hr, hw⟩ := parse_sound _ w hp
    exact h (render_injective_valid v w hw hr.symm ▸ hw)

end ExactJSON
