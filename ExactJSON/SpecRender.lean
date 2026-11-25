module

public import ExactJSON.Reread
public import ExactJSON.Text
public import ExactJSON.NumberText
public import ExactJSON.SpecValid
public import ExactJSON.DecimalText

public section

namespace ExactJSON

universe u

theorem array_push_eq {α : Type} (acc : Array α) (x : α) : acc.push x = ⟨acc.toList ++ [x]⟩ := by
  cases acc
  simp [Array.push]

def RestOk (rest : List Char) : Prop :=
  rest = [] ∨ ∃ c t, rest = c :: t ∧ (c = ',' ∨ c = ']' ∨ c = '}')

theorem RestOk.skipWs {rest : List Char} (h : RestOk rest) : Rfc8259.skipWs rest = rest := by
  rcases h with rfl | ⟨c, t, rfl, hc⟩
  · rfl
  · rcases hc with rfl | rfl | rfl <;> rfl

theorem RestOk.not_numberChar {rest : List Char} (h : RestOk rest) :
    ∀ c t, rest = c :: t → Rfc8259.isNumberChar c = false := by
  intro c t hct
  rcases h with rfl | ⟨d, u, rfl, hd⟩
  · cases hct
  · cases hct
    rcases hd with rfl | rfl | rfl <;> rfl

theorem skipWs_cons (c : Char) (t : List Char) (h : Rfc8259.isWs c = false) :
    Rfc8259.skipWs (c :: t) = c :: t := by
  simp [Rfc8259.skipWs, h]

theorem span_text (text rest : List Char) (htext : ∀ c ∈ text, Rfc8259.isNumberChar c = true)
    (hrest : RestOk rest) : (text ++ rest).span Rfc8259.isNumberChar = (text, rest) := by
  have := span_loop_text Rfc8259.isNumberChar text rest [] htext hrest.not_numberChar
  simpa [List.span] using this

theorem hexValue?_hexDigit : ∀ n, n < 16 → Rfc8259.hexValue? (hexDigit n) = some n := by decide

theorem mustEscape_lt {c : Char} (h : mustEscape c = true) : c.toNat < 0x2030 := by
  simp only [mustEscape, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  omega

theorem not_lt_of_mustEscape {c : Char} (h : mustEscape c = false) : ¬ c.val < 32 := by
  intro hlt
  have hl := UInt32.lt_iff_toNat_lt.mp hlt
  have : c.toNat < 32 := by simpa using hl
  simp only [mustEscape, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  exact h.1.1.1 this

theorem hex4?_escape (c : Char) (h : c.toNat < 0x10000) :
    Rfc8259.hex4? (hexDigit (c.toNat / 4096 % 16)) (hexDigit (c.toNat / 256 % 16)) (hexDigit (c.toNat / 16 % 16))
      (hexDigit (c.toNat % 16)) = some c.toNat := by
  simp only [Rfc8259.hex4?, hexValue?_hexDigit _ (Nat.mod_lt _ (by decide))]
  simp
  omega

theorem spec_chars_escape : ∀ (t rest acc : List Char),
    Rfc8259.chars (escapeList t ++ '"' :: rest) acc = .ok (acc.reverse ++ t, rest)
  | [], rest, acc => by simp [escapeList_nil, Rfc8259.chars]
  | c :: t, rest, acc => by
    have ih := spec_chars_escape t rest
    rw [escapeList_cons, List.append_assoc]
    unfold pushChar
    split
    · rename_i h
      have := beq_iff_eq.mp h
      subst this
      simp [Rfc8259.chars, Rfc8259.unescape?, ih]
    split
    · rename_i _ h
      have := beq_iff_eq.mp h
      subst this
      simp [Rfc8259.chars, Rfc8259.unescape?, ih]
    split
    · rename_i h1 h2 h3
      have n1 : c ≠ '"' := fun e => h1 (by simp [e])
      have n2 : c ≠ '\\' := fun e => h2 (by simp [e])
      have n3 : ¬ c.val < 32 := not_lt_of_mustEscape (by simpa using h3)
      simp only [String.toList_push, String.toList_empty, List.nil_append, List.singleton_append]
      rw [Rfc8259.chars.eq_5 _ _ _ (by simpa using n1) (by intro a b d e r h; simp_all)
        (by intro e r h; simp_all)]
      simp [n3, ih]
    rename_i h1 h2 h3
    have hm : mustEscape c = true := by simpa using h3
    split
    · rename_i h
      have := beq_iff_eq.mp h
      subst this
      simp [Rfc8259.chars, Rfc8259.unescape?, ih]
    split
    · rename_i h
      have := beq_iff_eq.mp h
      subst this
      simp [Rfc8259.chars, Rfc8259.unescape?, ih]
    split
    · rename_i h
      have := beq_iff_eq.mp h
      subst this
      simp [Rfc8259.chars, Rfc8259.unescape?, ih]
    split
    · rename_i h
      have := beq_iff_eq.mp h
      subst this
      simp [Rfc8259.chars, Rfc8259.unescape?, ih]
    split
    · rename_i h
      have := beq_iff_eq.mp h
      subst this
      simp [Rfc8259.chars, Rfc8259.unescape?, ih]
    · have hc : c.toNat < 0x2030 := mustEscape_lt hm
      simp only [String.toList_push, String.toList_append, List.append_assoc, List.cons_append]
      have hu : "\\u".toList = ['\\', 'u'] := by decide
      rw [hu]
      simp only [List.cons_append, List.nil_append, String.toList_empty]
      rw [Rfc8259.chars.eq_3, hex4?_escape c (by omega)]
      have hlt : (decide (c.toNat < 0xD800) || decide (0xE000 ≤ c.toNat)) = true := by
        simp
        omega
      simp only [hlt, ite_true, Char.ofNat_toNat, ih]
      simp

theorem render_integer_toList (n : Int) : (Value.render (.integer n)).toList = (toString n).toList := by
  simp [Value.render, Value.renderTo, intText_eq]

theorem render_decimal_toList (d : Decimal) : (Value.render (.decimal d)).toList = d.text.toList := by
  simp [Value.render, Value.renderTo]

theorem exists_cons_of_head? {l : List Char} {c : Char} (h : l.head? = some c) : ∃ t, l = c :: t := by
  cases l with
  | nil => cases h
  | cons d t =>
    simp only [List.head?_cons, Option.some.injEq] at h
    exact ⟨t, by rw [h]⟩

theorem toString_head (n : Int) : ∃ c, (toString n).toList.head? = some c ∧ (c = '-' ∨ c.isDigit = true) := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · rw [Nat.toList_repr]
    obtain ⟨c, t, h⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := n.toNat) (b := 10))
    exact ⟨c, by rw [h]; rfl,
      .inr (Nat.isDigit_of_mem_toDigits (b := 10) (n := n.toNat) (by decide) (by decide) (by rw [h]; simp))⟩
  · exact ⟨'-', by simp [String.toList_append], .inl rfl⟩

theorem decimalText_head (d : Decimal) :
    ∃ c, d.text.toList.head? = some c ∧ (c = '-' ∨ c.isDigit = true) := by
  obtain ⟨c0, t0, h0⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := d.digits) (b := 10))
  have hc0 : c0.isDigit = true :=
    Nat.isDigit_of_mem_toDigits (b := 10) (n := d.digits) (by decide) (by decide) (by rw [h0]; simp)
  unfold Decimal.text
  dsimp only
  cases hneg : d.negative
  · simp only [Bool.false_eq_true, ite_false, List.nil_append]
    split
    · exact ⟨'0', by simp, .inr rfl⟩
    · rw [String.toList_ofList, h0]
      split
      · split
        · exact ⟨c0, by simp, .inr hc0⟩
        · split
          · exact ⟨c0, by simp, .inr hc0⟩
          · exact ⟨'0', by simp, .inr rfl⟩
      · exact ⟨c0, by simp, .inr hc0⟩
  · simp only [ite_true]
    split
    · exact ⟨'-', by simp, .inl rfl⟩
    · exact ⟨'-', by simp, .inl rfl⟩

theorem spec_value_numberText (f : Nat) (text rest : List Char)
    (htext : ∀ c ∈ text, Rfc8259.isNumberChar c = true) (hne : text ≠ []) (hrest : RestOk rest) :
    Rfc8259.value (f + 1) (text ++ rest) =
      match Rfc8259.numberValue text with
      | .ok v => .ok (v, rest)
      | .error e => .error (e, text ++ rest) := by
  have hspan := span_text text rest htext hrest
  obtain ⟨c, t, rfl⟩ := List.exists_cons_of_ne_nil hne
  have hc := htext c (by simp)
  simp only [List.cons_append] at hspan ⊢
  unfold Rfc8259.value
  split
  all_goals first
    | (rename_i heq; simp only [List.cons.injEq] at heq; obtain ⟨rfl, -⟩ := heq; simp [Rfc8259.isNumberChar] at hc)
    | skip
  rw [hspan]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
  cases Rfc8259.numberValue (c :: t) <;> rfl

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} : x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

theorem head_ok_of_number (c : Char) (h : c = '-' ∨ c.isDigit = true) :
    Rfc8259.isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ ',' := by
  rcases h with rfl | h
  · decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Rfc8259.isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> (rintro rfl; simp at h)
    all_goals (rintro rfl; simp at h)

theorem render_head (v : Value) : ∃ c t, (Value.render v).toList = c :: t ∧
    Rfc8259.isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ ',' := by
  cases v with
  | null => exact ⟨'n', _, Value.text_null, by decide⟩
  | string s => exact ⟨'"', _, Value.text_string s, by decide⟩
  | integer n =>
    obtain ⟨c, hc, hk⟩ := toString_head n
    obtain ⟨t, ht⟩ := exists_cons_of_head? hc
    exact ⟨c, t, by rw [render_integer_toList, ht], head_ok_of_number c hk⟩
  | decimal d =>
    obtain ⟨c, hc, hk⟩ := decimalText_head d
    obtain ⟨t, ht⟩ := exists_cons_of_head? hc
    exact ⟨c, t, by rw [render_decimal_toList, ht], head_ok_of_number c hk⟩
  | boolean b => cases b <;> exact ⟨_, _, Value.text_boolean _, by decide⟩
  | array items =>
    cases items with
    | mk items => exact ⟨'[', _, Value.text_array items, by decide⟩
  | table members =>
    cases members with
    | mk members => exact ⟨'{', _, Value.text_table members, by decide⟩

theorem render_length_pos (v : Value) : 0 < (Value.render v).toList.length := by
  obtain ⟨c, t, h, -⟩ := render_head v
  rw [h]
  simp

theorem skipWs_render (v : Value) (rest : List Char) :
    Rfc8259.skipWs ((Value.render v).toList ++ rest) = (Value.render v).toList ++ rest := by
  obtain ⟨c, t, h, hws, -⟩ := render_head v
  rw [h, List.cons_append, skipWs_cons _ _ hws]

theorem spec_value_quote (f : Nat) (r : List Char) :
    Rfc8259.value (f + 1) ('"' :: r) =
      match Rfc8259.chars r [] with
      | .ok (cs, after) => .ok (.string (String.ofList cs), after)
      | .error e => .error e := by
  unfold Rfc8259.value
  rfl

theorem spec_value_bracket (f : Nat) (r : List Char) :
    Rfc8259.value (f + 1) ('[' :: r) =
      match Rfc8259.skipWs r with
      | ']' :: after => .ok (.array #[], after)
      | first => Rfc8259.elements f first #[] := by
  unfold Rfc8259.value
  rfl

theorem spec_value_brace (f : Nat) (r : List Char) :
    Rfc8259.value (f + 1) ('{' :: r) =
      match Rfc8259.skipWs r with
      | '}' :: after => .ok (.table #[], after)
      | first => Rfc8259.members f first #[] := by
  unfold Rfc8259.value
  rfl

theorem restOk_close (c : Char) (rest : List Char) (h : c = ',' ∨ c = ']' ∨ c = '}') : RestOk (c :: rest) :=
  .inr ⟨c, rest, rfl, h⟩

theorem itemsText_head (v : Value) (vs : List Value) : ∃ c t, Value.itemsText (v :: vs) = c :: t ∧
    Rfc8259.isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ ',' := by
  obtain ⟨c, t, h, hc⟩ := render_head v
  cases vs with
  | nil => exact ⟨c, t, by rw [Value.itemsText_singleton, h], hc⟩
  | cons w ws => exact ⟨c, _, by rw [Value.itemsText_cons, h, List.cons_append], hc⟩

theorem spec_open_array (f : Nat) (X : List Char) (c : Char) (t : List Char) (hX : X = c :: t)
    (hws : Rfc8259.isWs c = false) (hb : c ≠ ']') : Rfc8259.value (f + 1) ('[' :: X) = Rfc8259.elements f X #[] := by
  subst hX
  rw [spec_value_bracket, skipWs_cons _ _ hws]
  split
  · rename_i heq
    simp only [List.cons.injEq] at heq
    exact absurd heq.1 hb
  · rfl

theorem spec_open_table (f : Nat) (X : List Char) (t : List Char) (hX : X = '"' :: t) :
    Rfc8259.value (f + 1) ('{' :: X) = Rfc8259.members f X #[] := by
  subst hX
  rw [spec_value_brace, skipWs_cons _ _ (by decide)]
  rfl

theorem spec_table_sorted (l : List (String × Value)) (h : keysIncrease (l.map (·.1)) = true) :
    Rfc8259.table l = .ok (.table ⟨l⟩) := by
  unfold Rfc8259.table
  simp only [mergeSort_of_keysIncrease l h, neighboursDistinct_of_keysIncrease l h, ite_true]

theorem rereadMembers_keys : ∀ (ms ws : List (String × Value)), Value.rereadMembers ms = some ws →
    ws.map (·.1) = ms.map (·.1)
  | [], ws, h => by
    simp only [Value.rereadMembers, Option.some.injEq] at h
    subst h
    rfl
  | (k, v) :: ms, ws, h => by
    simp only [Value.rereadMembers] at h
    split at h
    · rename_i w us _ hus
      simp only [Option.some.injEq] at h
      subst h
      simp [rereadMembers_keys ms us hus]
    · cases h

theorem membersText_head (k : String) (v : Value) (ms : List (String × Value)) :
    ∃ t, Value.membersText ((k, v) :: ms) = '"' :: t := by
  cases ms with
  | nil => exact ⟨_, by rw [Value.membersText_singleton, Value.memberText]⟩
  | cons m ms => exact ⟨_, by rw [Value.membersText_cons, Value.memberText, List.cons_append]⟩

theorem keys_push_reread (acc : Array (String × Value)) (k : String) (v w : Value) (ms : List (String × Value)) :
    ((acc.push (k, w)).toList ++ ms).map (·.1) = (acc.toList ++ (k, v) :: ms).map (·.1) := by
  simp

mutual

theorem spec_render : (v : Value) → ∀ (fuel : Nat) (rest : List Char), RestOk rest → v.Valid →
    (Value.render v).toList.length ≤ fuel →
    (Rfc8259.value fuel ((Value.render v).toList ++ rest)).toOption = v.reread.map (·, rest)
  | v, 0, _, _, _, hlen => absurd hlen (by have := render_length_pos v; omega)
  | .null, f + 1, rest, _, _, _ => by
    rw [Value.text_null]
    rfl
  | .boolean b, f + 1, rest, _, _, _ => by
    cases b <;> (rw [Value.text_boolean]; rfl)
  | .string str, f + 1, rest, _, _, _ => by
    rw [Value.text_string]
    simp only [List.cons_append, List.append_assoc]
    rw [spec_value_quote, spec_chars_escape]
    simp [Value.reread, Except.toOption]
  | .integer n, f + 1, rest, hrest, _, _ => by
    rw [render_integer_toList, spec_value_numberText f _ rest (numberChars_toString n)
      (toString_toList_ne_nil n) hrest, numberValue_toString]
    rfl
  | .decimal d, f + 1, rest, hrest, _, _ => by
    rw [render_decimal_toList, spec_value_numberText f _ rest (numberChars_decimalText d) (decimalText_toList_ne_nil d) hrest]
    simp only [Value.reread, Value.rereadDecimal]
    cases Rfc8259.numberValue d.text.toList <;> rfl
  | .array ⟨[]⟩, f + 1, rest, _, _, _ => by
    rw [Value.text_array]
    simp only [Value.itemsText, Value.renderItems, String.toList_empty, List.nil_append, List.cons_append]
    rw [spec_value_bracket]
    simp [Rfc8259.skipWs, Value.reread, Value.rereadItems, Except.toOption]
    rfl
  | .array ⟨v :: vs⟩, f + 1, rest, hrest, hvalid, hlen => by
    have hvalid' : itemsValid (v :: vs) = true := hvalid
    rw [Value.text_array] at hlen ⊢
    simp only [List.length_cons, List.length_append] at hlen
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    obtain ⟨c, t, hct, hws, hb, -, -⟩ := itemsText_head v vs
    rw [spec_open_array f _ c (t ++ ']' :: rest) (by rw [hct, List.cons_append]) hws hb,
      spec_elements (v :: vs) f rest #[] (by simp) hrest hvalid' (by omega)]
    simp only [Value.reread, Option.map_map]
    rfl
  | .table ⟨[]⟩, f + 1, rest, _, _, _ => by
    rw [Value.text_table]
    simp only [Value.membersText, Value.renderMembers, String.toList_empty, List.nil_append, List.cons_append]
    rw [spec_value_brace]
    simp [Rfc8259.skipWs, Value.reread, Value.rereadMembers, Except.toOption]
    rfl
  | .table ⟨(k, v) :: ms⟩, f + 1, rest, hrest, hvalid, hlen => by
    have hvalid' : membersValid ((k, v) :: ms) = true := by
      have : (keysIncrease (((k, v) :: ms).map (·.1)) && membersValid ((k, v) :: ms)) = true := hvalid
      simp only [Bool.and_eq_true] at this
      exact this.2
    have hkeys : keysIncrease (((k, v) :: ms).map (·.1)) = true := by
      have : (keysIncrease (((k, v) :: ms).map (·.1)) && membersValid ((k, v) :: ms)) = true := hvalid
      simp only [Bool.and_eq_true] at this
      exact this.1
    rw [Value.text_table] at hlen ⊢
    simp only [List.length_cons, List.length_append] at hlen
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    obtain ⟨t, ht⟩ := membersText_head k v ms
    rw [spec_open_table f _ (t ++ '}' :: rest) (by rw [ht, List.cons_append]),
      spec_members ((k, v) :: ms) f rest #[] (by simp) hrest hvalid' (by simpa using hkeys) (by omega)]
    simp only [Value.reread, Option.map_map]
    rfl

theorem spec_elements : (items : List Value) → ∀ (fuel : Nat) (rest : List Char) (acc : Array Value),
    items ≠ [] → RestOk rest → itemsValid items = true → (Value.itemsText items).length + 1 ≤ fuel →
    (Rfc8259.elements fuel (Value.itemsText items ++ ']' :: rest) acc).toOption =
      (Value.rereadItems items).map fun ws => (.array ⟨acc.toList ++ ws⟩, rest)
  | [], _, _, _, hne, _, _, _ => absurd rfl hne
  | _ :: _, 0, _, _, _, _, _, hlen => absurd hlen (by omega)
  | [v], f + 1, rest, acc, _, hrest, hvalid, hlen => by
    have hv : v.Valid := by
      simp only [itemsValid, Bool.and_true] at hvalid
      exact hvalid
    rw [Value.itemsText_singleton] at hlen ⊢
    have ih := spec_render v f (']' :: rest) (restOk_close _ _ (by simp)) hv (by omega)
    rw [Rfc8259.elements.eq_2]
    cases hval : Rfc8259.value f ((Value.render v).toList ++ ']' :: rest) with
    | error e =>
      rw [hval] at ih
      simp only [Except.toOption] at ih
      have hre : v.reread = none := by
        cases h : v.reread with
        | none => rfl
        | some w => rw [h] at ih; cases ih
      simp [Value.rereadItems, hre, Except.toOption]
    | ok p =>
      obtain ⟨w, r⟩ := p
      rw [hval] at ih
      simp only [Except.toOption] at ih
      cases h : v.reread with
      | none => rw [h] at ih; cases ih
      | some w' =>
        rw [h] at ih
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ih
        obtain ⟨rfl, rfl⟩ := ih
        simp only
        rw [skipWs_cons ']' rest (by decide)]
        simp [Value.rereadItems, h, Except.toOption, array_push_eq]
  | v :: w :: ws, f + 1, rest, acc, _, hrest, hvalid, hlen => by
    have hv : v.Valid := by
      simp only [itemsValid, Bool.and_eq_true] at hvalid
      exact hvalid.1
    have hvalid' : itemsValid (w :: ws) = true := by
      simp only [itemsValid, Bool.and_eq_true] at hvalid ⊢
      exact hvalid.2
    rw [Value.itemsText_cons] at hlen ⊢
    simp only [List.length_append, List.length_cons] at hlen
    simp only [List.append_assoc, List.cons_append]
    have ih := spec_render v f (',' :: (Value.itemsText (w :: ws) ++ ']' :: rest)) (restOk_close _ _ (by simp)) hv
      (by omega)
    rw [Rfc8259.elements.eq_2]
    cases hval : Rfc8259.value f ((Value.render v).toList ++ ',' :: (Value.itemsText (w :: ws) ++ ']' :: rest)) with
    | error e =>
      rw [hval] at ih
      simp only [Except.toOption] at ih
      have hre : v.reread = none := by
        cases h : v.reread with
        | none => rfl
        | some u => rw [h] at ih; cases ih
      simp [Value.rereadItems, hre, Except.toOption]
    | ok p =>
      obtain ⟨u, r⟩ := p
      rw [hval] at ih
      simp only [Except.toOption] at ih
      cases h : v.reread with
      | none => rw [h] at ih; cases ih
      | some u' =>
        rw [h] at ih
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ih
        obtain ⟨rfl, rfl⟩ := ih
        obtain ⟨c, t, hct, hws, -⟩ := itemsText_head w ws
        simp only
        rw [skipWs_cons ',' _ (by decide)]
        simp only
        rw [show Rfc8259.skipWs (Value.itemsText (w :: ws) ++ ']' :: rest) =
            Value.itemsText (w :: ws) ++ ']' :: rest from by rw [hct, List.cons_append, skipWs_cons _ _ hws],
          spec_elements (w :: ws) f rest (acc.push u) (by simp) hrest hvalid' (by omega)]
        have hcons : Value.rereadItems (v :: w :: ws) =
            match v.reread, Value.rereadItems (w :: ws) with
            | some a, some b => some (a :: b)
            | _, _ => none := rfl
        rw [hcons, h]
        cases Value.rereadItems (w :: ws) <;> simp [array_push_eq]

theorem spec_members : (members : List (String × Value)) → ∀ (fuel : Nat) (rest : List Char)
    (acc : Array (String × Value)), members ≠ [] → RestOk rest → membersValid members = true →
    keysIncrease ((acc.toList ++ members).map (·.1)) = true → (Value.membersText members).length + 1 ≤ fuel →
    (Rfc8259.members fuel (Value.membersText members ++ '}' :: rest) acc).toOption =
      (Value.rereadMembers members).map fun ms => (.table ⟨acc.toList ++ ms⟩, rest)
  | [], _, _, _, hne, _, _, _, _ => absurd rfl hne
  | _ :: _, 0, _, _, _, _, _, _, hlen => absurd hlen (by omega)
  | [(k, v)], f + 1, rest, acc, _, hrest, hvalid, hkeys, hlen => by
    have hv : v.Valid := by
      simp only [membersValid, Bool.and_true] at hvalid
      exact hvalid
    rw [Value.membersText_singleton] at hlen ⊢
    simp only [Value.memberText, List.length_cons, List.length_append] at hlen
    simp only [Value.memberText, List.cons_append, List.append_assoc]
    have ih := spec_render v f ('}' :: rest) (restOk_close _ _ (by simp)) hv (by omega)
    rw [Rfc8259.members.eq_2, spec_chars_escape]
    simp only [List.reverse_nil, List.nil_append]
    rw [skipWs_cons ':' _ (by decide)]
    simp only
    rw [skipWs_render]
    cases hval : Rfc8259.value f ((Value.render v).toList ++ '}' :: rest) with
    | error e =>
      rw [hval] at ih
      simp only [Except.toOption] at ih
      have hre : v.reread = none := by
        cases h : v.reread with
        | none => rfl
        | some w => rw [h] at ih; cases ih
      simp [Value.rereadMembers, hre, Except.toOption]
    | ok p =>
      obtain ⟨w, r⟩ := p
      rw [hval] at ih
      simp only [Except.toOption] at ih
      cases h : v.reread with
      | none => rw [h] at ih; cases ih
      | some w' =>
        rw [h] at ih
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ih
        obtain ⟨rfl, rfl⟩ := ih
        simp only
        rw [skipWs_cons '}' rest (by decide)]
        simp only [String.ofList_toList]
        have hk : keysIncrease ((acc.push (k, w)).toList.map (·.1)) = true := by
          have := keys_push_reread acc k v w []
          rw [List.append_nil] at this
          rw [this]
          exact hkeys
        rw [spec_table_sorted _ hk]
        simp [Value.rereadMembers, h, Except.toOption]
  | (k, v) :: m :: ms, f + 1, rest, acc, _, hrest, hvalid, hkeys, hlen => by
    have hv : v.Valid := by
      simp only [membersValid, Bool.and_eq_true] at hvalid
      exact hvalid.1
    have hvalid' : membersValid (m :: ms) = true := by
      simp only [membersValid, Bool.and_eq_true] at hvalid ⊢
      exact hvalid.2
    rw [Value.membersText_cons] at hlen ⊢
    simp only [Value.memberText, List.length_cons, List.length_append] at hlen
    simp only [Value.memberText, List.cons_append, List.append_assoc]
    have ih := spec_render v f (',' :: (Value.membersText (m :: ms) ++ '}' :: rest)) (restOk_close _ _ (by simp)) hv
      (by omega)
    rw [Rfc8259.members.eq_2, spec_chars_escape]
    simp only [List.reverse_nil, List.nil_append]
    rw [skipWs_cons ':' _ (by decide)]
    simp only
    rw [skipWs_render]
    cases hval : Rfc8259.value f ((Value.render v).toList ++ ',' :: (Value.membersText (m :: ms) ++ '}' :: rest)) with
    | error e =>
      rw [hval] at ih
      simp only [Except.toOption] at ih
      have hre : v.reread = none := by
        cases h : v.reread with
        | none => rfl
        | some w => rw [h] at ih; cases ih
      simp [Value.rereadMembers, hre, Except.toOption]
    | ok p =>
      obtain ⟨w, r⟩ := p
      rw [hval] at ih
      simp only [Except.toOption] at ih
      cases h : v.reread with
      | none => rw [h] at ih; cases ih
      | some w' =>
        rw [h] at ih
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at ih
        obtain ⟨rfl, rfl⟩ := ih
        simp only
        rw [skipWs_cons ',' _ (by decide)]
        simp only
        obtain ⟨t, ht⟩ := membersText_head m.1 m.2 ms
        rw [show Rfc8259.skipWs (Value.membersText (m :: ms) ++ '}' :: rest) =
            Value.membersText (m :: ms) ++ '}' :: rest from by
              rw [show m = (m.1, m.2) from rfl, ht, List.cons_append, skipWs_cons _ _ (by decide)],
          String.ofList_toList,
          spec_members (m :: ms) f rest (acc.push (k, w)) (by simp) hrest hvalid'
            (by rw [keys_push_reread acc k v w (m :: ms)]; exact hkeys) (by omega)]
        have hcons : Value.rereadMembers ((k, v) :: m :: ms) =
            match v.reread, Value.rereadMembers (m :: ms) with
            | some a, some b => some ((k, a) :: b)
            | _, _ => none := rfl
        rw [hcons, h]
        cases Value.rereadMembers (m :: ms) <;> simp [array_push_eq]

end

theorem length_ofList_le_utf8ByteSize (l : List Char) : l.length ≤ (String.ofList l).utf8ByteSize := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton]
    have := Char.utf8Size_pos c
    simp only [List.length_cons]
    omega

theorem length_le_utf8ByteSize (s : String) : s.toList.length ≤ s.utf8ByteSize := by
  have := length_ofList_le_utf8ByteSize s.toList
  rwa [String.ofList_toList] at this

theorem read_of_reread (v : Value) (hvalid : v.Valid) (hre : v.reread = some v) :
    Rfc8259.read? v.render = some v := by
  have hlen := length_le_utf8ByteSize v.render
  have h := spec_render v (2 * v.render.utf8ByteSize + 2) [] (.inl rfl) hvalid (by omega)
  rw [hre, List.append_nil] at h
  simp only [Option.map_some] at h
  have h' := toOption_eq_some.mp h
  unfold Rfc8259.read? Rfc8259.read
  have hs : Rfc8259.skipWs v.render.toList = v.render.toList := by
    have := skipWs_render v []
    rwa [List.append_nil] at this
  rw [hs, h']
  rfl

mutual

theorem reread_self : (v : Value) → v.Valid → v.reread = some v
  | .null, _ => rfl
  | .string _, _ => rfl
  | .integer _, _ => rfl
  | .boolean _, _ => rfl
  | .decimal d, h => by
    simp only [Value.reread, Value.rereadDecimal, numberValue_text d]
  | .array ⟨items⟩, h => by
    simp only [Value.reread, rereadItems_self items h]
    rfl
  | .table ⟨members⟩, h => by
    have hboth : (keysIncrease (members.map (·.1)) && membersValid members) = true := h
    simp only [Bool.and_eq_true] at hboth
    simp only [Value.reread, rereadMembers_self members hboth.2]
    rfl

theorem rereadItems_self : (items : List Value) → itemsValid items = true → Value.rereadItems items = some items
  | [], _ => rfl
  | v :: vs, h => by
    simp only [itemsValid, Bool.and_eq_true] at h
    have hcons : Value.rereadItems (v :: vs) =
        match v.reread, Value.rereadItems vs with
        | some a, some b => some (a :: b)
        | _, _ => none := rfl
    rw [hcons, reread_self v h.1, rereadItems_self vs h.2]

theorem rereadMembers_self : (members : List (String × Value)) → membersValid members = true →
    Value.rereadMembers members = some members
  | [], _ => rfl
  | (k, v) :: ms, h => by
    simp only [membersValid, Bool.and_eq_true] at h
    have hcons : Value.rereadMembers ((k, v) :: ms) =
        match v.reread, Value.rereadMembers ms with
        | some a, some b => some ((k, a) :: b)
        | _, _ => none := rfl
    rw [hcons, reread_self (k, v).2 h.1, rereadMembers_self ms h.2]

end

theorem spec_read_render (v : Value) (h : v.Valid) : Rfc8259.read? v.render = some v :=
  read_of_reread v h (reread_self v h)

end ExactJSON
