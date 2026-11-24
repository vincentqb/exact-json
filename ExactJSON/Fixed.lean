module

public import ExactJSON.Sound
public import ExactJSON.NumberText
public import ExactJSON.SpecValid

/-! # Canonical texts are the fixed points of reading JSON

RFC 8259 reads a valid value's text as the value with its floats read back (`Value.reread`), and
the strict reader reads that text as the value when its floats read back as themselves. Together
with soundness, which says the strict reader only reads such texts, this gives `parse_fixed`.
-/

public section

namespace ExactJSON

universe u

/-- What may follow a value in canonical text: nothing, or `,`, `]` or `}`. -/
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

theorem span_loop_text (p : Char → Bool) : ∀ (text rest acc : List Char), (∀ c ∈ text, p c = true) →
    (∀ c t, rest = c :: t → p c = false) → List.span.loop p (text ++ rest) acc = (acc.reverse ++ text, rest)
  | [], rest, acc, _, hrest => by
    cases rest with
    | nil => simp [List.span.loop]
    | cons c t => simp [List.span.loop, hrest c t rfl]
  | c :: text, rest, acc, htext, hrest => by
    simp only [List.cons_append, List.span.loop, htext c (by simp)]
    rw [span_loop_text p text rest (c :: acc) (fun d hd => htext d (by simp [hd])) hrest]
    simp

theorem span_text (text rest : List Char) (htext : ∀ c ∈ text, Rfc8259.isNumberChar c = true)
    (hrest : RestOk rest) : (text ++ rest).span Rfc8259.isNumberChar = (text, rest) := by
  have := span_loop_text Rfc8259.isNumberChar text rest [] htext hrest.not_numberChar
  simpa [List.span] using this

theorem hexValue?_hexDigit : ∀ n, n < 16 → Rfc8259.hexValue? (hexDigit n) = some n := by decide

theorem hex4?_control (c : Char) (h : c.toNat < 0x20) :
    Rfc8259.hex4? '0' '0' (hexDigit (c.toNat / 16)) (hexDigit (c.toNat % 16)) = some c.toNat := by
  simp only [Rfc8259.hex4?, hexValue?_hexDigit _ (by omega : c.toNat / 16 < 16),
    hexValue?_hexDigit _ (Nat.mod_lt _ (by decide))]
  simp only [Rfc8259.hexValue?]
  simp
  omega

/-- RFC 8259 reads a string's escaped characters back. -/
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
      have n3 : ¬ c.val < 32 := by
        have := UInt32.le_iff_toNat_le.mp h3
        intro hlt
        have := UInt32.lt_iff_toNat_lt.mp hlt
        simp at *
        omega
      simp only [String.toList_push, String.toList_empty, List.nil_append, List.singleton_append]
      rw [Rfc8259.chars.eq_5 _ _ _ (by simpa using n1) (by intro a b d e r h; simp_all)
        (by intro e r h; simp_all)]
      simp [n3, ih]
    rename_i h1 h2 h3
    have n3 : c.val < 32 := by
      have := UInt32.not_le.mp h3
      exact this
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
    · have hc : c.toNat < 0x20 := by
        have := UInt32.lt_iff_toNat_lt.mp n3
        simpa using this
      simp only [String.toList_push, String.toList_append, List.append_assoc, List.cons_append]
      have hu : "\\u00".toList = ['\\', 'u', '0', '0'] := by decide
      rw [hu]
      simp only [List.cons_append, List.nil_append, String.toList_empty]
      rw [Rfc8259.chars.eq_3, hex4?_control c hc]
      have hlt : (decide (c.toNat < 0xD800) || decide (0xE000 ≤ c.toNat)) = true := by
        simp
        omega
      simp only [hlt, ite_true, Char.ofNat_toNat, ih]
      simp

theorem parser_hexValue_hexDigit : ∀ n, n < 16 → Parser.hexValue (hexDigit n) = some n := by decide

theorem parser_hex4_control (c : Char) (h : c.toNat < 0x20) :
    Parser.hex4 '0' '0' (hexDigit (c.toNat / 16)) (hexDigit (c.toNat % 16)) = some c.toNat := by
  simp only [Parser.hex4, parser_hexValue_hexDigit _ (by omega : c.toNat / 16 < 16),
    parser_hexValue_hexDigit _ (Nat.mod_lt _ (by decide))]
  simp only [Parser.hexValue]
  simp
  omega

theorem string_push_ofList (acc : String) (c : Char) (t : List Char) :
    acc.push c ++ String.ofList t = acc ++ String.ofList (c :: t) := by
  apply String.ext
  simp [String.toList_append, String.toList_push]

theorem strict_string_quote (rest : List Char) (acc : String) (s0 : Nat) :
    Parser.string ('"' :: rest) acc s0 = .ok acc rest (s0 + 1) := by
  rw [Parser.string.eq_def]
  simp

theorem strict_string_raw (c : Char) (X : List Char) (acc : String) (s0 : Nat) (h1 : ¬(c == '"') = true)
    (h2 : ¬(c == '\\') = true) (n3 : ¬ c.val < 32) :
    Parser.string (c :: X) acc s0 = Parser.string X (acc.push c) (s0 + 1) := by
  rw [Parser.string.eq_def]
  simp only
  split <;> simp_all

theorem strict_string_short (e c : Char) (X : List Char) (acc : String) (s0 : Nat)
    (hu : Parser.unescape e = some c) (he : e ≠ 'u') :
    Parser.string ('\\' :: e :: X) acc s0 = Parser.string X (acc.push c) (s0 + 2) := by
  rw [Parser.string.eq_def]
  simp only
  split <;> simp_all

theorem strict_string_control (c : Char) (X : List Char) (acc : String) (s0 : Nat) (hc : c.toNat < 0x20)
    (hpush : (pushChar "" c).toList = ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]) :
    Parser.string ((pushChar "" c).toList ++ X) acc s0 = Parser.string X (acc.push c) (s0 + 12) := by
  rw [hpush, Parser.string.eq_def]
  simp only [List.cons_append, List.nil_append]
  simp only [beq_self_eq_true, ite_true]
  have hq : ('\\' == '"') = false := by decide
  simp only [hq, Bool.false_eq_true, ite_false]
  rw [parser_hex4_control c hc]
  have hs : (decide (55296 ≤ c.toNat) && decide (c.toNat < 57344)) = false := by
    simp
    omega
  simp only [hs, Bool.false_eq_true, ite_false, Char.ofNat_toNat]
  have hw : (pushChar "" c == String.ofList ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]) = true := by
    rw [beq_iff_eq]
    apply String.ext
    rw [hpush, String.toList_ofList]
  simp only [hw, ite_true]

/-- The strict reader reads a string's escaped characters back. -/
theorem strict_string_escape : ∀ (t rest : List Char) (acc : String) (s0 : Nat),
    ∃ s, Parser.string (escapeList t ++ '"' :: rest) acc s0 = .ok (acc ++ String.ofList t) rest s
  | [], rest, acc, s0 => ⟨s0 + 1, by simp [escapeList_nil, strict_string_quote]⟩
  | c :: t, rest, acc, s0 => by
    have ih := strict_string_escape t rest
    rw [escapeList_cons, List.append_assoc]
    have step : ∀ k, Parser.string ((pushChar "" c).toList ++ (escapeList t ++ '"' :: rest)) acc s0 =
        Parser.string (escapeList t ++ '"' :: rest) (acc.push c) (s0 + k) →
        ∃ s, Parser.string ((pushChar "" c).toList ++ (escapeList t ++ '"' :: rest)) acc s0 =
          .ok (acc ++ String.ofList (c :: t)) rest s := by
      intro k hk
      obtain ⟨s, hs⟩ := ih (acc.push c) (s0 + k)
      exact ⟨s, by rw [hk, hs, string_push_ofList]⟩
    by_cases h1 : (c == '"') = true
    · have := beq_iff_eq.mp h1
      subst this
      exact step 2 (strict_string_short '"' '"' _ acc s0 rfl (by decide))
    by_cases h2 : (c == '\\') = true
    · have := beq_iff_eq.mp h2
      subst this
      exact step 2 (strict_string_short '\\' '\\' _ acc s0 rfl (by decide))
    by_cases h3 : c.val ≥ 32
    · have n3 : ¬ c.val < 32 := by
        have := UInt32.le_iff_toNat_le.mp h3
        intro hlt
        have := UInt32.lt_iff_toNat_lt.mp hlt
        simp at *
        omega
      have hp : (pushChar "" c).toList = [c] := by simp [pushChar, h1, h2, h3]
      exact step 1 (by rw [hp, List.singleton_append]; exact strict_string_raw c _ acc s0 h1 h2 n3)
    have n3 : c.val < 32 := UInt32.not_le.mp h3
    have hc : c.toNat < 0x20 := by
      have := UInt32.lt_iff_toNat_lt.mp n3
      simpa using this
    by_cases h4 : (c == '\x08') = true
    · have := beq_iff_eq.mp h4
      subst this
      exact step 2 (strict_string_short 'b' '\x08' _ acc s0 rfl (by decide))
    by_cases h5 : (c == '\t') = true
    · have := beq_iff_eq.mp h5
      subst this
      exact step 2 (strict_string_short 't' '\t' _ acc s0 rfl (by decide))
    by_cases h6 : (c == '\n') = true
    · have := beq_iff_eq.mp h6
      subst this
      exact step 2 (strict_string_short 'n' '\n' _ acc s0 rfl (by decide))
    by_cases h7 : (c == '\x0c') = true
    · have := beq_iff_eq.mp h7
      subst this
      exact step 2 (strict_string_short 'f' '\x0c' _ acc s0 rfl (by decide))
    by_cases h8 : (c == '\r') = true
    · have := beq_iff_eq.mp h8
      subst this
      exact step 2 (strict_string_short 'r' '\r' _ acc s0 rfl (by decide))
    have hpush : (pushChar "" c).toList =
        ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)] := by
      simp only [pushChar, h1, h2, h3, h4, h5, h6, h7, h8]
      simp
    exact step 12 (strict_string_control c _ acc s0 hc hpush)

theorem render_integer_toList (n : Int) : (Value.render (.integer n)).toList = (toString n).toList := by
  simp [Value.render, Value.renderTo]

theorem render_float_toList (x : Float) : (Value.render (.float x)).toList = (floatText x).toList := by
  simp [Value.render, Value.renderTo]

/-- A float's text is a decimal's, or the token of a NaN or an infinity. -/
theorem floatText_cases (x : Float) :
    (∃ d : Decimal, (floatText x).toList = d.toFloatText.toList) ∨ (floatText x).toList = "NaN".toList ∨
      (floatText x).toList = "Infinity".toList ∨ (floatText x).toList = "-Infinity".toList := by
  unfold floatText
  split
  · rename_i text h
    left
    unfold Float.toCanonical? at h
    cases hs : FloatText.shortest x with
    | none => simp [hs] at h
    | some d =>
      simp only [hs, Option.map_some, Option.some.injEq] at h
      exact ⟨d, by rw [h]⟩
  · right
    split
    · exact .inl rfl
    · split
      · exact .inr (.inl rfl)
      · exact .inr (.inr rfl)

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

theorem toFloatText_head (d : Decimal) :
    ∃ c, d.toFloatText.toList.head? = some c ∧ (c = '-' ∨ c.isDigit = true) := by
  obtain ⟨c0, t0, h0⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := d.digits) (b := 10))
  have hc0 : c0.isDigit = true :=
    Nat.isDigit_of_mem_toDigits (b := 10) (n := d.digits) (by decide) (by decide) (by rw [h0]; simp)
  unfold Decimal.toFloatText
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

/-- RFC 8259 reads a number's text, the whole of it, as `numberValue` does. -/
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

theorem spec_value_floatText_none (f : Nat) (x : Float) (rest : List Char)
    (h : (floatText x).toList = "NaN".toList ∨ (floatText x).toList = "Infinity".toList ∨
      (floatText x).toList = "-Infinity".toList) :
    (Rfc8259.value (f + 1) ((floatText x).toList ++ rest)).toOption = none ∧ Value.rereadFloat x = none := by
  have nan : ∀ rest : List Char, (Rfc8259.value (f + 1) ("NaN".toList ++ rest)).toOption = none := by
    intro rest
    unfold Rfc8259.value
    simp [List.span, List.span.loop, Rfc8259.isNumberChar, Except.toOption]
  have inf : ∀ rest : List Char, (Rfc8259.value (f + 1) ("Infinity".toList ++ rest)).toOption = none := by
    intro rest
    unfold Rfc8259.value
    simp [List.span, List.span.loop, Rfc8259.isNumberChar, Except.toOption]
  have minf : ∀ rest : List Char, (Rfc8259.value (f + 1) ("-Infinity".toList ++ rest)).toOption = none := by
    intro rest
    unfold Rfc8259.value
    simp [List.span, List.span.loop, Rfc8259.isNumberChar, Except.toOption, Rfc8259.numberValue, Rfc8259.numberSign]
  rcases h with h | h | h
  · exact ⟨by rw [h]; exact nan rest, by simp only [Value.rereadFloat, h]; rfl⟩
  · exact ⟨by rw [h]; exact inf rest, by simp only [Value.rereadFloat, h]; rfl⟩
  · exact ⟨by rw [h]; exact minf rest, by simp only [Value.rereadFloat, h]; rfl⟩

theorem toOption_eq_some {ε α : Type} {x : Except ε α} {a : α} : x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

theorem toOption_eq_none {ε α : Type} {x : Except ε α} : x.toOption = none ↔ ∃ e, x = .error e := by
  cases x <;> simp [Except.toOption]

theorem head_ok_of_number (c : Char) (h : c = '-' ∨ c.isDigit = true) :
    Rfc8259.isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ ',' := by
  rcases h with rfl | h
  · decide
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Rfc8259.isWs, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩ <;> (rintro rfl; simp at h)
    all_goals (rintro rfl; simp at h)

/-- A canonical text starts with no whitespace and no closing character. -/
theorem render_head (v : Value) : ∃ c t, (Value.render v).toList = c :: t ∧
    Rfc8259.isWs c = false ∧ c ≠ ']' ∧ c ≠ '}' ∧ c ≠ ',' := by
  cases v with
  | null => exact ⟨'n', _, Value.text_null, by decide⟩
  | string s => exact ⟨'"', _, Value.text_string s, by decide⟩
  | integer n =>
    obtain ⟨c, hc, hk⟩ := toString_head n
    obtain ⟨t, ht⟩ := exists_cons_of_head? hc
    exact ⟨c, t, by rw [render_integer_toList, ht], head_ok_of_number c hk⟩
  | float x =>
    rcases floatText_cases x with ⟨d, hd⟩ | h | h | h
    · obtain ⟨c, hc, hk⟩ := toFloatText_head d
      obtain ⟨t, ht⟩ := exists_cons_of_head? hc
      exact ⟨c, t, by rw [render_float_toList, hd, ht], head_ok_of_number c hk⟩
    · exact ⟨'N', _, by rw [render_float_toList, h]; rfl, by decide⟩
    · exact ⟨'I', _, by rw [render_float_toList, h]; rfl, by decide⟩
    · exact ⟨'-', _, by rw [render_float_toList, h]; rfl, by decide⟩
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

/-- The table of members whose keys increase is those members. -/
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

/-- RFC 8259 reads a valid value's text as the value with its floats read back. -/
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
  | .float x, f + 1, rest, hrest, _, _ => by
    rw [render_float_toList]
    rcases floatText_cases x with ⟨d, hd⟩ | h
    · rw [hd, spec_value_numberText f _ rest (numberChars_toFloatText d) (toFloatText_toList_ne_nil d) hrest]
      simp only [Value.reread, Value.rereadFloat, hd]
      cases Rfc8259.numberValue d.toFloatText.toList <;> rfl
    · obtain ⟨h1, h2⟩ := spec_value_floatText_none f x rest h
      rw [h1]
      simp [Value.reread, h2]
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

/-- RFC 8259 reads an array's items, from the first, with their floats read back. -/
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
        simp [Value.rereadItems, h, Except.toOption, Parser.array_push_eq]
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
        cases Value.rereadItems (w :: ws) <;> simp [Parser.array_push_eq]

/-- RFC 8259 reads a table's members, from the first, with their floats read back. -/
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
        cases Value.rereadMembers (m :: ms) <;> simp [Parser.array_push_eq]

end

/-! ## The strict reader reads a canonical text whose floats read back -/

theorem strict_value_number (f s0 : Nat) (c : Char) (t : List Char) (hc : c = '-' ∨ c.isDigit = true) :
    Parser.value (f + 1) (c :: t) s0 = Parser.number (c :: t) s0 := by
  have ne : ∀ d : Char, (d = '"' ∨ d = '[' ∨ d = '{' ∨ d = 'n' ∨ d = 't' ∨ d = 'f') → c ≠ d := by
    rintro d hd rfl
    rcases hc with h | h <;> rcases hd with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
  rw [Parser.value.eq_11 _ _ _ _ (ne _ (by simp)) (fun _ h _ => ne _ (by simp) h) (ne _ (by simp))
    (fun _ h _ => ne _ (by simp) h) (ne _ (by simp)) (fun _ h _ => ne _ (by simp) h)
    (fun _ h _ => ne _ (by simp) h) (fun _ h _ => ne _ (by simp) h)]
  have : (c == '-' || c.isDigit) = true := by
    rcases hc with rfl | h
    · rfl
    · simp [h]
  simp [this]

theorem strict_number_text (s0 : Nat) (text rest : List Char) (v : Value)
    (htext : ∀ c ∈ text, Rfc8259.isNumberChar c = true) (hrest : RestOk rest)
    (hv : Rfc8259.numberValue text = .ok v) (hr : (Value.render v).toList = text) :
    ∃ s, Parser.number (text ++ rest) s0 = .ok v rest s := by
  unfold Parser.number
  rw [span_text text rest htext hrest]
  simp only [hv]
  exact ⟨s0 + 7 * text.length + 7, by simp [hr]⟩

theorem rereadItems_cons {v : Value} {vs ws : List Value} (h : Value.rereadItems (v :: vs) = some ws) :
    ∃ w us, v.reread = some w ∧ Value.rereadItems vs = some us ∧ ws = w :: us := by
  have hcons : Value.rereadItems (v :: vs) =
      match v.reread, Value.rereadItems vs with
      | some a, some b => some (a :: b)
      | _, _ => none := rfl
  rw [hcons] at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, ha, hb, rfl⟩
  · cases h

theorem rereadMembers_cons {k : String} {v : Value} {ms ws : List (String × Value)}
    (h : Value.rereadMembers ((k, v) :: ms) = some ws) :
    ∃ w us, v.reread = some w ∧ Value.rereadMembers ms = some us ∧ ws = (k, w) :: us := by
  have hcons : Value.rereadMembers ((k, v) :: ms) =
      match v.reread, Value.rereadMembers ms with
      | some a, some b => some ((k, a) :: b)
      | _, _ => none := rfl
  rw [hcons] at h
  split at h
  · rename_i a b ha hb
    cases h
    exact ⟨a, b, ha, hb, rfl⟩
  · cases h

theorem keysIncreaseFrom_prefix : ∀ (p : String) (l1 l2 : List String),
    keysIncreaseFrom p (l1 ++ l2) = true → keysIncreaseFrom p l1 = true
  | _, [], _, _ => rfl
  | p, a :: l1, l2, h => by
    simp only [List.cons_append, keysIncreaseFrom, Bool.and_eq_true] at h ⊢
    exact ⟨h.1, keysIncreaseFrom_prefix a l1 l2 h.2⟩

theorem keysIncrease_prefix (l1 l2 : List String) (h : keysIncrease (l1 ++ l2) = true) :
    keysIncrease l1 = true := by
  cases l1 with
  | nil => rfl
  | cons a l1 =>
    simp only [List.cons_append, keysIncrease] at h ⊢
    exact keysIncreaseFrom_prefix a l1 l2 h

theorem keyFollows_of_keysIncrease (acc : Array (String × Value)) (k : String) (v : Value)
    (ms : List (String × Value)) (h : keysIncrease ((acc.toList ++ (k, v) :: ms).map (·.1)) = true) :
    Parser.keyFollows acc k = true := by
  have h1 : keysIncrease (acc.toList.map (·.1) ++ [k]) = true := by
    apply keysIncrease_prefix _ (ms.map (·.1))
    simpa using h
  unfold Parser.keyFollows
  rw [← Array.getLast?_toList]
  cases hl : acc.toList with
  | nil => rfl
  | cons a l =>
    rw [hl] at h1
    simp only [List.map_cons, List.cons_append, keysIncrease] at h1
    have h2 := ((keysIncreaseFrom_append _ _ _).mp h1).2
    cases hlast : (a :: l).getLast? with
    | none => simp at hlast
    | some q =>
      obtain ⟨p, w⟩ := q
      simp only
      have hp : (l.map (·.1)).getLast?.getD a.1 = p := by
        have := congrArg (Option.map (·.1)) hlast
        simp only [List.getLast?_cons, Option.map_some] at this
        rw [List.getLast?_map]
        cases hl' : l.getLast? with
        | none => simp [hl'] at this ⊢; exact this
        | some r => simp [hl'] at this ⊢; exact this
      rw [hp] at h2
      exact decide_eq_true h2

theorem strict_open_array (f s0 : Nat) (X : List Char) (c : Char) (t : List Char) (hX : X = c :: t)
    (hb : c ≠ ']') : Parser.value (f + 1) ('[' :: X) s0 = Parser.items f X #[] (s0 + 1) := by
  subst hX
  rw [Parser.value.eq_5]
  intro r h
  simp only [List.cons.injEq] at h
  exact hb h.1

theorem strict_open_table (f s0 : Nat) (t : List Char) :
    Parser.value (f + 1) ('{' :: '"' :: t) s0 = Parser.members f ('"' :: t) #[] (s0 + 1) := by
  rw [Parser.value.eq_7]
  intro r h
  simp at h

theorem float_reread_text {x : Float} (h : Value.rereadFloat x = some (.float x)) :
    ∃ d : Decimal, (floatText x).toList = d.toFloatText.toList := by
  rcases floatText_cases x with hd | hn
  · exact hd
  · have := (spec_value_floatText_none 0 x [] hn).2
    rw [this] at h
    cases h

theorem rereadFloat_numberValue {x : Float} (h : Value.rereadFloat x = some (.float x)) :
    Rfc8259.numberValue (floatText x).toList = .ok (.float x) := by
  unfold Value.rereadFloat at h
  split at h
  · rename_i w hw
    cases h
    exact hw
  · cases h

mutual

/-- The strict reader reads a valid value's text when its floats read back as themselves. -/
theorem strict_render : (v : Value) → ∀ (fuel s0 : Nat) (rest : List Char), RestOk rest → v.Valid →
    v.reread = some v → (Value.render v).toList.length ≤ fuel →
    ∃ s, Parser.value fuel ((Value.render v).toList ++ rest) s0 = .ok v rest s
  | v, 0, _, _, _, _, _, hlen => absurd hlen (by have := render_length_pos v; omega)
  | .null, f + 1, s0, rest, _, _, _, _ => ⟨s0 + 4, by rw [Value.text_null]; rfl⟩
  | .boolean b, f + 1, s0, rest, _, _, _, _ => by
    cases b
    · exact ⟨s0 + 5, by rw [Value.text_boolean]; rfl⟩
    · exact ⟨s0 + 4, by rw [Value.text_boolean]; rfl⟩
  | .string str, f + 1, s0, rest, _, _, _, _ => by
    rw [Value.text_string]
    simp only [List.cons_append, List.append_assoc]
    obtain ⟨s, hs⟩ := strict_string_escape str.toList rest "" (s0 + 1)
    refine ⟨s, ?_⟩
    rw [Parser.value.eq_3]
    simp only [List.nil_append, hs]
    simp
  | .integer n, f + 1, s0, rest, hrest, _, _, _ => by
    rw [render_integer_toList]
    obtain ⟨c, hc, hk⟩ := toString_head n
    obtain ⟨t, ht⟩ := exists_cons_of_head? hc
    rw [ht, List.cons_append, strict_value_number f s0 c _ hk, ← List.cons_append, ← ht]
    exact strict_number_text s0 _ rest _ (numberChars_toString n) hrest (numberValue_toString n)
      (render_integer_toList n)
  | .float x, f + 1, s0, rest, hrest, _, hre, _ => by
    have hre' : Value.rereadFloat x = some (.float x) := hre
    obtain ⟨d, hd⟩ := float_reread_text hre'
    rw [render_float_toList, hd]
    obtain ⟨c, hc, hk⟩ := toFloatText_head d
    obtain ⟨t, ht⟩ := exists_cons_of_head? hc
    rw [ht, List.cons_append, strict_value_number f s0 c _ hk, ← List.cons_append, ← ht]
    exact strict_number_text s0 _ rest _ (numberChars_toFloatText d) hrest
      (by rw [← hd]; exact rereadFloat_numberValue hre') (by rw [render_float_toList, hd])
  | .array ⟨[]⟩, f + 1, s0, rest, _, _, _, _ => ⟨s0 + 2, by
      rw [Value.text_array]
      rfl⟩
  | .array ⟨v :: vs⟩, f + 1, s0, rest, hrest, hvalid, hre, hlen => by
    have hvalid' : itemsValid (v :: vs) = true := hvalid
    have hre' : Value.rereadItems (v :: vs) = some (v :: vs) := by
      simp only [Value.reread] at hre
      cases h : Value.rereadItems (v :: vs) with
      | none => rw [h] at hre; cases hre
      | some ws =>
        rw [h] at hre
        simp only [Option.map_some, Option.some.injEq, Value.array.injEq, Array.mk.injEq] at hre
        rw [hre]
    rw [Value.text_array] at hlen ⊢
    simp only [List.length_cons, List.length_append] at hlen
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    obtain ⟨c, t, hct, -, hb, -, -⟩ := itemsText_head v vs
    rw [strict_open_array f s0 _ c (t ++ ']' :: rest) (by rw [hct, List.cons_append]) hb]
    obtain ⟨s, hs⟩ := strict_items (v :: vs) f (s0 + 1) rest #[] (by simp) hrest hvalid' hre' (by omega)
    exact ⟨s, by rw [hs]; rfl⟩
  | .table ⟨[]⟩, f + 1, s0, rest, _, _, _, _ => ⟨s0 + 2, by
      rw [Value.text_table]
      rfl⟩
  | .table ⟨(k, v) :: ms⟩, f + 1, s0, rest, hrest, hvalid, hre, hlen => by
    have hboth : (keysIncrease (((k, v) :: ms).map (·.1)) && membersValid ((k, v) :: ms)) = true := hvalid
    simp only [Bool.and_eq_true] at hboth
    have hre' : Value.rereadMembers ((k, v) :: ms) = some ((k, v) :: ms) := by
      simp only [Value.reread] at hre
      cases h : Value.rereadMembers ((k, v) :: ms) with
      | none => rw [h] at hre; cases hre
      | some ws =>
        rw [h] at hre
        simp only [Option.map_some, Option.some.injEq, Value.table.injEq, Array.mk.injEq] at hre
        rw [hre]
    rw [Value.text_table] at hlen ⊢
    simp only [List.length_cons, List.length_append] at hlen
    simp only [List.cons_append, List.append_assoc, List.nil_append]
    obtain ⟨t, ht⟩ := membersText_head k v ms
    rw [ht, List.cons_append, strict_open_table, ← List.cons_append, ← ht]
    obtain ⟨s, hs⟩ := strict_members ((k, v) :: ms) f (s0 + 1) rest #[] (by simp) hrest hboth.2
      (by simpa using hboth.1) hre' (by omega)
    exact ⟨s, by rw [hs]; rfl⟩

/-- The strict reader reads an array's items, from the first. -/
theorem strict_items : (items : List Value) → ∀ (fuel s0 : Nat) (rest : List Char) (acc : Array Value),
    items ≠ [] → RestOk rest → itemsValid items = true → Value.rereadItems items = some items →
    (Value.itemsText items).length + 1 ≤ fuel →
    ∃ s, Parser.items fuel (Value.itemsText items ++ ']' :: rest) acc s0 = .ok (.array ⟨acc.toList ++ items⟩) rest s
  | [], _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | _ :: _, 0, _, _, _, _, _, _, _, hlen => absurd hlen (by omega)
  | [v], f + 1, s0, rest, acc, _, hrest, hvalid, hre, hlen => by
    have hv : v.Valid := by
      simp only [itemsValid, Bool.and_true] at hvalid
      exact hvalid
    obtain ⟨w, us, hw, -, hws⟩ := rereadItems_cons hre
    simp only [List.cons.injEq] at hws
    obtain ⟨rfl, -⟩ := hws
    rw [Value.itemsText_singleton] at hlen ⊢
    obtain ⟨s1, hs1⟩ := strict_render v f s0 (']' :: rest) (restOk_close _ _ (by simp)) hv hw (by omega)
    refine ⟨s1 + 1, ?_⟩
    rw [Parser.items.eq_2, hs1]
    simp [Parser.array_push_eq]
  | v :: w :: ws, f + 1, s0, rest, acc, _, hrest, hvalid, hre, hlen => by
    have hv : v.Valid := by
      simp only [itemsValid, Bool.and_eq_true] at hvalid
      exact hvalid.1
    have hvalid' : itemsValid (w :: ws) = true := by
      simp only [itemsValid, Bool.and_eq_true] at hvalid ⊢
      exact hvalid.2
    obtain ⟨u, us, hu, hus, hws⟩ := rereadItems_cons hre
    simp only [List.cons.injEq] at hws
    obtain ⟨rfl, rfl⟩ := hws
    rw [Value.itemsText_cons] at hlen ⊢
    simp only [List.length_append, List.length_cons] at hlen
    simp only [List.append_assoc, List.cons_append]
    obtain ⟨s1, hs1⟩ := strict_render v f s0 (',' :: (Value.itemsText (w :: ws) ++ ']' :: rest))
      (restOk_close _ _ (by simp)) hv hu (by omega)
    obtain ⟨s2, hs2⟩ := strict_items (w :: ws) f (s1 + 1) rest (acc.push v) (by simp) hrest hvalid' hus (by omega)
    refine ⟨s2, ?_⟩
    rw [Parser.items.eq_2, hs1]
    simp only
    rw [hs2]
    simp [Parser.array_push_eq]

/-- The strict reader reads a table's members, from the first, keys increasing after `acc`'s. -/
theorem strict_members : (members : List (String × Value)) → ∀ (fuel s0 : Nat) (rest : List Char)
    (acc : Array (String × Value)), members ≠ [] → RestOk rest → membersValid members = true →
    keysIncrease ((acc.toList ++ members).map (·.1)) = true → Value.rereadMembers members = some members →
    (Value.membersText members).length + 1 ≤ fuel →
    ∃ s, Parser.members fuel (Value.membersText members ++ '}' :: rest) acc s0 =
      .ok (.table ⟨acc.toList ++ members⟩) rest s
  | [], _, _, _, _, hne, _, _, _, _, _ => absurd rfl hne
  | _ :: _, 0, _, _, _, _, _, _, _, _, hlen => absurd hlen (by omega)
  | [(k, v)], f + 1, s0, rest, acc, _, hrest, hvalid, hkeys, hre, hlen => by
    have hv : v.Valid := by
      simp only [membersValid, Bool.and_true] at hvalid
      exact hvalid
    obtain ⟨w, us, hw, -, hws⟩ := rereadMembers_cons hre
    simp only [List.cons.injEq, Prod.mk.injEq, true_and] at hws
    obtain ⟨rfl, -⟩ := hws
    rw [Value.membersText_singleton] at hlen ⊢
    simp only [Value.memberText, List.length_cons, List.length_append] at hlen
    simp only [Value.memberText, List.cons_append, List.append_assoc]
    obtain ⟨ks, hks⟩ := strict_string_escape k.toList (':' :: ((Value.render v).toList ++ '}' :: rest)) "" 0
    obtain ⟨s1, hs1⟩ := strict_render v f (s0 + 1 + 2 * ks + 1) ('}' :: rest) (restOk_close _ _ (by simp)) hv hw
      (by omega)
    refine ⟨s1 + 1, ?_⟩
    rw [Parser.members.eq_2, hks]
    simp only [String.empty_append, String.ofList_toList]
    rw [keyFollows_of_keysIncrease acc k v [] hkeys]
    simp only [ite_true]
    rw [hs1]
    simp [Parser.array_push_eq]
  | (k, v) :: m :: ms, f + 1, s0, rest, acc, _, hrest, hvalid, hkeys, hre, hlen => by
    have hv : v.Valid := by
      simp only [membersValid, Bool.and_eq_true] at hvalid
      exact hvalid.1
    have hvalid' : membersValid (m :: ms) = true := by
      simp only [membersValid, Bool.and_eq_true] at hvalid ⊢
      exact hvalid.2
    obtain ⟨w, us, hw, hus, hws⟩ := rereadMembers_cons hre
    simp only [List.cons.injEq, Prod.mk.injEq, true_and] at hws
    obtain ⟨rfl, rfl⟩ := hws
    rw [Value.membersText_cons] at hlen ⊢
    simp only [Value.memberText, List.length_cons, List.length_append] at hlen
    simp only [Value.memberText, List.cons_append, List.append_assoc]
    obtain ⟨ks, hks⟩ := strict_string_escape k.toList
      (':' :: ((Value.render v).toList ++ ',' :: (Value.membersText (m :: ms) ++ '}' :: rest))) "" 0
    obtain ⟨s1, hs1⟩ := strict_render v f (s0 + 1 + 2 * ks + 1) (',' :: (Value.membersText (m :: ms) ++ '}' :: rest))
      (restOk_close _ _ (by simp)) hv hw (by omega)
    obtain ⟨s2, hs2⟩ := strict_members (m :: ms) f (s1 + 1) rest (acc.push (k, v)) (by simp) hrest hvalid'
      (by simpa using hkeys) hus (by omega)
    refine ⟨s2, ?_⟩
    rw [Parser.members.eq_2, hks]
    simp only [String.empty_append, String.ofList_toList]
    rw [keyFollows_of_keysIncrease acc k v (m :: ms) hkeys]
    simp only [ite_true]
    rw [hs1]
    simp only
    rw [hs2]
    simp [Parser.array_push_eq]

end

/-! ## The fixed points -/

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

/-- RFC 8259 reads a valid value's text as the value, when its floats read back. -/
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

/-- What RFC 8259 reads in a valid value's text is that value only if its floats read back. -/
theorem reread_of_read (v : Value) (hvalid : v.Valid) (h : Rfc8259.read? v.render = some v) :
    v.reread = some v := by
  have hlen := length_le_utf8ByteSize v.render
  have hspec := spec_render v (2 * v.render.utf8ByteSize + 2) [] (.inl rfl) hvalid (by omega)
  rw [List.append_nil] at hspec
  have hs : Rfc8259.skipWs v.render.toList = v.render.toList := by
    have := skipWs_render v []
    rwa [List.append_nil] at this
  unfold Rfc8259.read? Rfc8259.read at h
  rw [hs] at h
  cases hval : Rfc8259.value (2 * v.render.utf8ByteSize + 2) v.render.toList with
  | error e =>
    rw [hval] at h
    cases h
  | ok p =>
    obtain ⟨w, r⟩ := p
    rw [hval] at h hspec
    simp only [Except.toOption] at hspec
    simp only at h
    split at h
    · simp only [Except.toOption, Option.some.injEq] at h
      cases hre : v.reread with
      | none => rw [hre] at hspec; cases hspec
      | some u =>
        rw [hre] at hspec
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hspec
        rw [← hspec.1, h]
    · cases h

/-- The strict reader reads a valid value's text, when its floats read back. -/
theorem parse_render_of_reread (v : Value) (hvalid : v.Valid) (hre : v.reread = some v) :
    Value.parse v.render = .ok v := by
  have hlen := length_le_utf8ByteSize v.render
  obtain ⟨s, hs⟩ := strict_render v (2 * v.render.utf8ByteSize + 2) v.render.utf8ByteSize [] (.inl rfl) hvalid hre
    (by omega)
  rw [List.append_nil] at hs
  unfold Value.parse Value.parseCosted
  simp only
  rw [hs]

/-- A canonical text is exactly a JSON text that writing what it holds gives back. -/
theorem parse_fixed (s : String) (v : Value) :
    Value.parse s = .ok v ↔ Rfc8259.read? s = some v ∧ v.render = s := by
  constructor
  · intro h
    obtain ⟨hr, hvalid⟩ := parse_sound s v h
    have hre := parse_reread s v h
    refine ⟨?_, hr⟩
    rw [← hr]
    exact read_of_reread v hvalid hre
  · rintro ⟨hread, hr⟩
    subst hr
    have hvalid := Rfc8259.read?_valid _ _ hread
    exact parse_render_of_reread v hvalid (reread_of_read v hvalid hread)

/-! ## What remains: every finite float reads back from its text -/

/-- Every finite float is read back from its canonical text. -/
@[expose] def FloatsReadBack : Prop := ∀ x : Float, finiteFloat x = true → Value.rereadFloat x = some (.float x)

section Floats


mutual

theorem reread_self (floats : FloatsReadBack) : (v : Value) → v.Valid → v.reread = some v
  | .null, _ => rfl
  | .string _, _ => rfl
  | .integer _, _ => rfl
  | .boolean _, _ => rfl
  | .float x, h => floats x h
  | .array ⟨items⟩, h => by
    simp only [Value.reread, rereadItems_self floats items h]
    rfl
  | .table ⟨members⟩, h => by
    have hboth : (keysIncrease (members.map (·.1)) && membersValid members) = true := h
    simp only [Bool.and_eq_true] at hboth
    simp only [Value.reread, rereadMembers_self floats members hboth.2]
    rfl

theorem rereadItems_self (floats : FloatsReadBack) : (items : List Value) → itemsValid items = true → Value.rereadItems items = some items
  | [], _ => rfl
  | v :: vs, h => by
    simp only [itemsValid, Bool.and_eq_true] at h
    have hcons : Value.rereadItems (v :: vs) =
        match v.reread, Value.rereadItems vs with
        | some a, some b => some (a :: b)
        | _, _ => none := rfl
    rw [hcons, reread_self floats v h.1, rereadItems_self floats vs h.2]

theorem rereadMembers_self (floats : FloatsReadBack) : (members : List (String × Value)) → membersValid members = true →
    Value.rereadMembers members = some members
  | [], _ => rfl
  | (k, v) :: ms, h => by
    simp only [membersValid, Bool.and_eq_true] at h
    have hcons : Value.rereadMembers ((k, v) :: ms) =
        match v.reread, Value.rereadMembers ms with
        | some a, some b => some ((k, a) :: b)
        | _, _ => none := rfl
    rw [hcons, reread_self floats (k, v).2 h.1, rereadMembers_self floats ms h.2]

end

/-- `read_render`, from the float lemma. -/
theorem read_render_of_floats (floats : FloatsReadBack) (v : Value) (h : v.Valid) : Rfc8259.read? v.render = some v :=
  read_of_reread v h (reread_self floats v h)

/-- Every valid value is read back from its text, from the float lemma. -/
theorem render_parse_of_floats (floats : FloatsReadBack) (v : Value) (h : v.Valid) : Value.parse v.render = .ok v :=
  parse_render_of_reread v h (reread_self floats v h)

/-- `decode_encode`, from the float lemma. -/
theorem decode_encode_of_floats (floats : FloatsReadBack) {α : Type u} [ToValue α] [FromValue α]
    (lawful : ∀ a : α, fromValue? (toValue a) = .ok a) (valid : ∀ a : α, (toValue a).Valid) (a : α) :
    decode (encode a) = .ok a := by
  unfold decode encode
  rw [render_parse_of_floats floats _ (valid a)]
  simp only [lawful a]
  have : (toValue a == toValue a) = true := Value.beq_self (toValue a)
  simp [this]

end Floats

end ExactJSON
