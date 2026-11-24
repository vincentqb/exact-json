module

public import ExactJSON.DateTime

public section

namespace ExactJSON

private def LocalDate.isValid (d : LocalDate) : Bool :=
  d.year ≤ 9999 && 1 ≤ d.month && d.month ≤ 12 && 1 ≤ d.day && d.day ≤ daysInMonth d.year d.month

private def LocalTime.isValid (t : LocalTime) : Bool :=
  t.hour ≤ 23 && t.minute ≤ 59 && t.second ≤ 60 && t.nanosecond < 1000000000

private def LocalDateTime.isValid (dt : LocalDateTime) : Bool := dt.date.isValid && dt.time.isValid

private def OffsetDateTime.isValid (dt : OffsetDateTime) : Bool :=
  dt.date.isValid && dt.time.isValid && dt.offsetMinutes.natAbs < 24 * 60

private def DateTime.isValid : DateTime → Bool
  | .offsetDateTime dt => dt.isValid
  | .localDateTime dt => dt.isValid
  | .localDate d => d.isValid
  | .localTime t => t.isValid

private theorem LocalDate.isValid_true (d : LocalDate) : d.isValid = true := by
  obtain ⟨_, _, _, h1, h2, h3, h4, h5⟩ := d
  simp [LocalDate.isValid, h1, h2, h3, h4, h5]

private theorem LocalTime.isValid_true (t : LocalTime) : t.isValid = true := by
  obtain ⟨_, _, _, _, h1, h2, h3, h4⟩ := t
  simp [LocalTime.isValid, h1, h2, h3, h4]

private theorem DateTime.isValid_true (d : DateTime) : d.isValid = true := by
  cases d with
  | offsetDateTime dt =>
    simp [DateTime.isValid, OffsetDateTime.isValid, LocalDate.isValid_true, LocalTime.isValid_true, dt.valid]
  | localDateTime dt => simp [DateTime.isValid, LocalDateTime.isValid, LocalDate.isValid_true, LocalTime.isValid_true]
  | localDate d => exact d.isValid_true
  | localTime t => exact t.isValid_true

theorem localDate_text (d : LocalDate) : d.toString = d.text := rfl

theorem localTime_text (t : LocalTime) : t.toString = t.text := by
  have h := t.isValid_true
  have hns : t.nanosecond < 1000000000 := by
    simp only [LocalTime.isValid, Bool.and_eq_true, decide_eq_true_eq] at h
    omega
  unfold LocalTime.toString LocalTime.text Calendar.fraction
  by_cases h0 : t.nanosecond = 0
  · simp only [h0, beq_self_eq_true, ite_true, String.append_empty]
    rfl
  · simp only [h0, Nat.not_le.mpr hns, beq_iff_eq, ite_false]
    rw [String.append_assoc]
    rfl

theorem localDateTime_text (dt : LocalDateTime) : dt.toString = dt.text := by
  unfold LocalDateTime.toString LocalDateTime.text
  rw [← localDate_text dt.date, ← localTime_text dt.time]
  rfl

private theorem offsetText_eq (m : Int) : offsetText m = Calendar.offset m := by
  unfold offsetText Calendar.offset
  by_cases h0 : m = 0
  · simp [h0]
  · simp only [h0, beq_iff_eq, ite_false]
    rfl

theorem offsetDateTime_text (dt : OffsetDateTime) : dt.toString = dt.text := by
  unfold OffsetDateTime.toString OffsetDateTime.text
  rw [← localDate_text dt.date, ← localTime_text dt.time, ← offsetText_eq]
  rfl

theorem dateTime_text (d : DateTime) : d.toString = d.text := by
  cases d with
  | offsetDateTime dt => exact offsetDateTime_text dt
  | localDateTime dt => exact localDateTime_text dt
  | localDate d => exact localDate_text d
  | localTime t => exact localTime_text t

namespace DateText

private theorem digits_value (l : List Char) :
    l.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0 = Nat.ofDigitChars 10 l 0 := by
  rw [Nat.ofDigitChars_eq_foldl]
  congr 1
  funext acc c
  rw [Nat.mul_comm]
  rfl

private theorem pad_toList (w n : Nat) :
    (Calendar.pad w n).toList = List.replicate (w - (Nat.toDigits 10 n).length) '0' ++ Nat.toDigits 10 n := by
  simp [Calendar.pad]

private theorem pad_length (w n : Nat) (hw : 0 < w) (h : n < 10 ^ w) : (Calendar.pad w n).toList.length = w := by
  rw [pad_toList, List.length_append, List.length_replicate]
  have := (Nat.length_toDigits_le_iff (by decide) hw).mpr h
  omega

private theorem pad_isDigit (w n : Nat) : ∀ c ∈ (Calendar.pad w n).toList, c.isDigit = true := by
  rw [pad_toList]
  intro c hc
  rcases List.mem_append.mp hc with h | h
  · rw [List.eq_of_mem_replicate h]
    rfl
  · exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) h

private theorem pad_value (w n : Nat) : Nat.ofDigitChars 10 (Calendar.pad w n).toList 0 = n := by
  rw [pad_toList, Nat.ofDigitChars_append, Nat.ofDigitChars_replicate_zero, Nat.mul_zero,
    Nat.ofDigitChars_ten_toDigits]

private theorem fixed_pad (w n : Nat) (hw : 0 < w) (h : n < 10 ^ w) (rest : List Char) :
    fixed w ((Calendar.pad w n).toList ++ rest) = some (n, rest) := by
  have hl := pad_length w n hw h
  unfold fixed
  simp only
  rw [List.take_left' hl, List.drop_left' hl, hl, digits_value, pad_value]
  simp [List.all_eq_true.mpr (pad_isDigit w n)]

private theorem lit_cons (c : Char) (rest : List Char) : lit c (c :: rest) = some rest := by
  simp [lit]

private theorem localDate_text_toList (d : LocalDate) :
    d.text.toList = (Calendar.pad 4 d.year).toList ++ '-' :: ((Calendar.pad 2 d.month).toList ++ '-' ::
      (Calendar.pad 2 d.day).toList) := by
  simp [LocalDate.text, String.toList_append]

private theorem date_text (d : LocalDate) (h : d.isValid = true) (rest : List Char) :
    date (d.text.toList ++ rest) = some (d, rest) := by
  have hv := h
  simp only [LocalDate.isValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hdim : daysInMonth d.year d.month ≤ 31 := by
    unfold daysInMonth
    split
    · split <;> omega
    · split <;> omega
  rw [localDate_text_toList]
  simp only [List.append_assoc, List.cons_append]
  unfold date
  rw [fixed_pad 4 d.year (by decide) (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, lit_cons]
  rw [fixed_pad 2 d.month (by decide) (by omega)]
  simp only [Option.bind_some, lit_cons]
  rw [fixed_pad 2 d.day (by decide) (by omega)]
  simp only [Option.bind_some]
  rw [dite_eq_left d.valid]

private theorem trailing_zeros (l : List Char) :
    (l.reverse.dropWhile (· = '0')).reverse ++
      List.replicate (l.length - (l.reverse.dropWhile (· = '0')).reverse.length) '0' = l := by
  have h1 := List.takeWhile_append_dropWhile (p := fun c => decide (c = '0')) (l := l.reverse)
  have hT : l.reverse.takeWhile (fun c => decide (c = '0')) =
      List.replicate (l.reverse.takeWhile (fun c => decide (c = '0'))).length '0' := by
    rw [List.eq_replicate_iff]
    refine ⟨rfl, fun b hb => ?_⟩
    have := List.all_eq_true.mp List.all_takeWhile b hb
    simpa using this
  have hlen := congrArg List.length h1
  simp only [List.length_append, List.length_reverse] at hlen
  conv => rhs; rw [← List.reverse_reverse l, ← h1]
  rw [List.reverse_append, hT, List.reverse_replicate, List.length_reverse]
  congr 2
  omega

private theorem fraction_digits (ns : Nat) (h0 : ns ≠ 0) (h1 : ns < 1000000000) :
    ((Calendar.pad 9 ns).toList.reverse.dropWhile (· = '0')).reverse ≠ [] ∧
      ((Calendar.pad 9 ns).toList.reverse.dropWhile (· = '0')).reverse.length ≤ 9 ∧
      (∀ c ∈ ((Calendar.pad 9 ns).toList.reverse.dropWhile (· = '0')).reverse, c.isDigit = true) ∧
      ((Calendar.pad 9 ns).toList.reverse.dropWhile (· = '0')).reverse ++
        List.replicate (9 - ((Calendar.pad 9 ns).toList.reverse.dropWhile (· = '0')).reverse.length) '0' =
        (Calendar.pad 9 ns).toList := by
  have hl := pad_length 9 ns (by decide) h1
  have hz := trailing_zeros (Calendar.pad 9 ns).toList
  rw [hl] at hz
  refine ⟨fun hnil => ?_, ?_, fun c hc => ?_, hz⟩
  · rw [hnil, List.nil_append, List.length_nil] at hz
    have := pad_value 9 ns
    rw [← hz, Nat.ofDigitChars_replicate_zero] at this
    omega
  · rw [List.length_reverse]
    have := (List.dropWhile_sublist (fun c => decide (c = '0')) (l := (Calendar.pad 9 ns).toList.reverse)).length_le
    rw [List.length_reverse, hl] at this
    exact this
  · rw [List.mem_reverse] at hc
    exact pad_isDigit 9 ns c (List.mem_reverse.mp (List.dropWhile_subset _ hc))

private theorem localTime_text_toList (t : LocalTime) :
    t.text.toList = (Calendar.pad 2 t.hour).toList ++ ':' :: ((Calendar.pad 2 t.minute).toList ++ ':' ::
      ((Calendar.pad 2 t.second).toList ++ (Calendar.fraction t.nanosecond).toList)) := by
  simp [LocalTime.text, String.toList_append]

private theorem fraction_toList (ns : Nat) :
    (Calendar.fraction ns).toList =
      if ns = 0 then [] else '.' :: ((Calendar.pad 9 ns).toList.reverse.dropWhile (· = '0')).reverse := by
  unfold Calendar.fraction
  split <;> simp

private theorem time_text (t : LocalTime) (h : t.isValid = true) (rest : List Char)
    (hrest : ∀ c ∈ rest.head?, c ≠ '.' ∧ c.isDigit = false) :
    time (t.text.toList ++ rest) = some (t, rest) := by
  obtain ⟨hour, minute, second, ns, hvalid⟩ := t
  have hv := h
  simp only [LocalTime.isValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [localTime_text_toList]
  simp only [List.append_assoc, List.cons_append]
  unfold time
  rw [fixed_pad 2 hour (by decide) (by omega)]
  simp only [Option.bind_eq_bind, Option.bind_some, lit_cons]
  rw [fixed_pad 2 minute (by decide) (by omega)]
  simp only [Option.bind_some, lit_cons]
  rw [fixed_pad 2 second (by decide) (by omega)]
  simp only [Option.bind_some]
  rw [fraction_toList]
  have htw : List.takeWhile Char.isDigit rest = [] := by
    cases rest with
    | nil => rfl
    | cons c cs => exact List.takeWhile_cons_of_neg (by simp [(hrest c rfl).2])
  by_cases h0 : ns = 0
  · subst h0
    have hlit : lit '.' rest = none := by
      cases rest with
      | nil => rfl
      | cons c cs =>
        have := (hrest c rfl).1
        simp [lit, Ne.symm this]
    simp only [ite_true, List.nil_append, hlit]
    rw [dite_eq_left hvalid]
  · obtain ⟨hne, hlen, hdig, hpad⟩ := fraction_digits ns h0 hv.2
    simp only [h0, ite_false, List.cons_append, lit_cons]
    rw [List.takeWhile_append_of_pos hdig, htw, List.append_nil, List.drop_left' rfl, hpad, digits_value, pad_value]
    have hne' : (((Calendar.pad 9 ns).toList.reverse.dropWhile (· = '0')).reverse.isEmpty ||
        decide (((Calendar.pad 9 ns).toList.reverse.dropWhile (· = '0')).reverse.length > 9)) = false := by
      simp only [Bool.or_eq_false_iff, List.isEmpty_eq_false_iff, decide_eq_false_iff_not]
      exact ⟨hne, by omega⟩
    rw [hne']
    simp only [Bool.false_eq_true, ite_false]
    rw [dite_eq_left hvalid]

private theorem offset_text (o : Int) (h : o.natAbs < 24 * 60) : offset (Calendar.offset o).toList = some (o, []) := by
  unfold Calendar.offset
  by_cases h0 : o = 0
  · subst h0
    rfl
  · have h1 : o.natAbs / 60 < 10 ^ 2 := by omega
    have h2 : o.natAbs % 60 < 10 ^ 2 := by omega
    have hsign : ∀ s : Char, (s = '-' ∧ o < 0 ∨ s = '+' ∧ ¬o < 0) →
        offset (s :: ((Calendar.pad 2 (o.natAbs / 60)).toList ++ ':' :: (Calendar.pad 2 (o.natAbs % 60)).toList)) =
          some (o, []) := by
      intro s hs
      have hZ : s ≠ 'Z' := by rcases hs with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      have hpm : (s == '+' || s == '-') = true := by rcases hs with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
      unfold offset
      split
      · rename_i heq
        simp only [List.cons.injEq] at heq
        exact absurd heq.1 hZ
      · rename_i s' rest' _ heq
        simp only [List.cons.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        rw [ite_eq_left hpm, fixed_pad 2 _ (by decide) h1]
        simp only [Option.bind_eq_bind, Option.bind_some, lit_cons]
        rw [← List.append_nil (Calendar.pad 2 (o.natAbs % 60)).toList, fixed_pad 2 _ (by decide) h2]
        simp only [Option.bind_some]
        rw [ite_eq_left (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)]
        rcases hs with ⟨rfl, hneg⟩ | ⟨rfl, hpos⟩
        · simp only [show ('-' == '-') = true by decide, ite_true, Option.some.injEq, Prod.mk.injEq, and_true]
          omega
        · simp only [show ('+' == '-') = false by decide, Bool.false_eq_true, ite_false, Option.some.injEq,
            Prod.mk.injEq, and_true]
          omega
      · rename_i heq
        simp at heq
    by_cases hneg : o < 0
    · simp only [h0, hneg, ite_false, ite_true, String.toList_append, List.append_assoc,
        show "-".toList = ['-'] by rfl, show ":".toList = [':'] by rfl, List.cons_append, List.nil_append]
      exact hsign '-' (Or.inl ⟨rfl, hneg⟩)
    · simp only [h0, hneg, ite_false, String.toList_append, List.append_assoc,
        show "+".toList = ['+'] by rfl, show ":".toList = [':'] by rfl, List.cons_append, List.nil_append]
      exact hsign '+' (Or.inr ⟨rfl, hneg⟩)

private theorem fixed_four_none (h : Nat) (hh : h < 10 ^ 2) (rest : List Char) :
    fixed 4 ((Calendar.pad 2 h).toList ++ ':' :: rest) = none := by
  have hl := pad_length 2 h (by decide) hh
  have hd : ':'.isDigit = false := by decide
  unfold fixed
  simp only
  rw [List.take_append, List.take_of_length_le (by omega), hl]
  simp [List.all_append, hd]

private theorem date_none_of_time (t : LocalTime) (h : t.isValid = true) (rest : List Char) :
    date (t.text.toList ++ rest) = none := by
  have hv := h
  simp only [LocalTime.isValid, Bool.and_eq_true, decide_eq_true_eq] at hv
  rw [localTime_text_toList]
  simp only [List.append_assoc, List.cons_append]
  unfold date
  rw [fixed_four_none t.hour (by omega)]
  rfl

private theorem offset_head (o : Int) :
    ∃ c cs, (Calendar.offset o).toList = c :: cs ∧ ∀ x ∈ (c :: cs).head?, x ≠ '.' ∧ x.isDigit = false := by
  unfold Calendar.offset
  by_cases h0 : o = 0
  · exact ⟨'Z', [], by simp [h0], by simp⟩
  · by_cases hneg : o < 0
    · exact ⟨'-', _, by simp [h0, hneg, String.toList_append]; rfl, by simp⟩
    · exact ⟨'+', _, by simp [h0, hneg, String.toList_append]; rfl, by simp⟩

private theorem shape_text (d : DateTime) (h : d.isValid = true) : shape d.text = some d := by
  cases d with
  | localDate dd =>
    unfold shape
    simp only [DateTime.text]
    rw [← List.append_nil dd.text.toList, date_text dd h]
  | localDateTime dt =>
    obtain ⟨dd, tt⟩ := dt
    simp only [DateTime.isValid, LocalDateTime.isValid, Bool.and_eq_true] at h
    unfold shape
    simp only [DateTime.text, LocalDateTime.text, String.toList_append, show "T".toList = ['T'] by rfl,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [date_text dd h.1]
    simp only
    rw [← List.append_nil tt.text.toList, time_text tt h.2 [] (by simp)]
  | offsetDateTime dt =>
    obtain ⟨dd, tt, o, ho⟩ := dt
    simp only [DateTime.isValid, OffsetDateTime.isValid, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨c, cs, hoff, hhead⟩ := offset_head o
    unfold shape
    simp only [DateTime.text, OffsetDateTime.text, String.toList_append, show "T".toList = ['T'] by rfl,
      List.append_assoc, List.cons_append, List.nil_append]
    rw [date_text dd h.1.1]
    simp only
    rw [time_text tt h.1.2 _ (by rw [hoff]; exact hhead), hoff]
    simp only
    rw [← hoff, offset_text o h.2]
    simp only
    rw [dite_eq_left ho]
  | localTime tt =>
    unfold shape
    simp only [DateTime.text]
    rw [← List.append_nil tt.text.toList, date_none_of_time tt h, time_text tt h [] (by simp)]

end DateText

theorem dateTime_parse (s : String) (d : DateTime) : DateTime.parse? s = some d ↔ d.text = s := by
  unfold DateTime.parse?
  rw [Option.filter_eq_some_iff]
  constructor
  · rintro ⟨_, he⟩
    rw [← dateTime_text d]
    simpa using he
  · rintro rfl
    refine ⟨DateText.shape_text d d.isValid_true, ?_⟩
    simp [dateTime_text d]

private theorem fromValue_dateTime (w : Value) (d : DateTime) :
    (fromValue? w : Except String DateTime) = .ok d ↔ w = .string d.text := by
  cases w with
  | string s =>
    show (match DateTime.parse? s with
      | some dt => pure dt
      | none => typeMismatch "a date-time, date or time in canonical RFC 3339 form" (.string s)) = _ ↔ _
    rw [Value.string.injEq]
    cases hp : DateTime.parse? s with
    | none =>
      simp only [typeMismatch, reduceCtorEq, false_iff]
      intro he
      subst he
      rw [(dateTime_parse d.text d).mpr rfl] at hp
      cases hp
    | some dt =>
      have := dateTime_parse s dt
      rw [hp] at this
      simp only [pure, Except.pure, Except.ok.injEq]
      constructor
      · rintro rfl
        exact (this.mp rfl).symm
      · rintro rfl
        have := (dateTime_parse d.text d).mpr rfl
        rw [hp] at this
        exact Option.some.inj this
  | _ => simp [fromValue?, typeMismatch]

theorem codec_dateTime (d : DateTime) :
    toValue d = .string d.toString ∧ ∀ w : Value, fromValue? w = .ok d ↔ w = .string d.text :=
  ⟨rfl, fun w => fromValue_dateTime w d⟩

private theorem fromValue_localDate (w : Value) (d : LocalDate) :
    (fromValue? w : Except String LocalDate) = .ok d ↔
      (fromValue? w : Except String DateTime) = .ok (.localDate d) := by
  show (do
    match ← (fromValue? w : Except String DateTime) with
    | .localDate d => pure d
    | _ => typeMismatch "a date (YYYY-MM-DD)" w) = _ ↔ _
  generalize (fromValue? w : Except String DateTime) = r
  cases r with
  | error e => simp [bind, Except.bind]
  | ok dt => cases dt <;> simp [bind, Except.bind, pure, Except.pure, typeMismatch]

theorem codec_localDate (d : LocalDate) :
    toValue d = .string d.toString ∧ ∀ w : Value, fromValue? w = .ok d ↔ w = .string d.text :=
  ⟨rfl, fun w => (fromValue_localDate w d).trans (fromValue_dateTime w (.localDate d))⟩

private theorem fromValue_localTime (w : Value) (t : LocalTime) :
    (fromValue? w : Except String LocalTime) = .ok t ↔
      (fromValue? w : Except String DateTime) = .ok (.localTime t) := by
  show (do
    match ← (fromValue? w : Except String DateTime) with
    | .localTime t => pure t
    | _ => typeMismatch "a time of day (HH:MM:SS)" w) = _ ↔ _
  generalize (fromValue? w : Except String DateTime) = r
  cases r with
  | error e => simp [bind, Except.bind]
  | ok dt => cases dt <;> simp [bind, Except.bind, pure, Except.pure, typeMismatch]

theorem codec_localTime (t : LocalTime) :
    toValue t = .string t.toString ∧ ∀ w : Value, fromValue? w = .ok t ↔ w = .string t.text :=
  ⟨rfl, fun w => (fromValue_localTime w t).trans (fromValue_dateTime w (.localTime t))⟩

private theorem fromValue_localDateTime (w : Value) (dt : LocalDateTime) :
    (fromValue? w : Except String LocalDateTime) = .ok dt ↔
      (fromValue? w : Except String DateTime) = .ok (.localDateTime dt) := by
  show (do
    match ← (fromValue? w : Except String DateTime) with
    | .localDateTime dt => pure dt
    | _ => typeMismatch "a local date-time (no offset)" w) = _ ↔ _
  generalize (fromValue? w : Except String DateTime) = r
  cases r with
  | error e => simp [bind, Except.bind]
  | ok d => cases d <;> simp [bind, Except.bind, pure, Except.pure, typeMismatch]

theorem codec_localDateTime (dt : LocalDateTime) :
    toValue dt = .string dt.toString ∧ ∀ w : Value, fromValue? w = .ok dt ↔ w = .string dt.text :=
  ⟨rfl, fun w => (fromValue_localDateTime w dt).trans (fromValue_dateTime w (.localDateTime dt))⟩

private theorem fromValue_offsetDateTime (w : Value) (dt : OffsetDateTime) :
    (fromValue? w : Except String OffsetDateTime) = .ok dt ↔
      (fromValue? w : Except String DateTime) = .ok (.offsetDateTime dt) := by
  show (do
    match ← (fromValue? w : Except String DateTime) with
    | .offsetDateTime dt => pure dt
    | _ => typeMismatch "an offset date-time (with Z or ±HH:MM)" w) = _ ↔ _
  generalize (fromValue? w : Except String DateTime) = r
  cases r with
  | error e => simp [bind, Except.bind]
  | ok d => cases d <;> simp [bind, Except.bind, pure, Except.pure, typeMismatch]

theorem codec_offsetDateTime (dt : OffsetDateTime) :
    toValue dt = .string dt.toString ∧ ∀ w : Value, fromValue? w = .ok dt ↔ w = .string dt.text :=
  ⟨rfl, fun w => (fromValue_offsetDateTime w dt).trans (fromValue_dateTime w (.offsetDateTime dt))⟩

private theorem empty_ne_localDate_text (d : LocalDate) : "" ≠ d.text := by
  intro h
  have := congrArg String.toList h
  rw [DateText.localDate_text_toList] at this
  simp at this

private theorem empty_ne_localTime_text (t : LocalTime) : "" ≠ t.text := by
  intro h
  have := congrArg String.toList h
  rw [DateText.localTime_text_toList] at this
  simp at this

private theorem empty_ne_append {s t : String} (h : "" ≠ s) : "" ≠ s ++ t := by
  intro he
  have := congrArg String.length he
  rw [String.length_append] at this
  have hs : s.length = 0 := by simp at this; omega
  exact h (String.length_eq_zero_iff.mp hs).symm

theorem localDate_text_rejects_empty :
    ¬ ∀ (d : LocalDate), (fun (_ : LocalDate) => "") d = d.text := by
  intro h
  exact empty_ne_localDate_text _ (h default)

theorem localTime_text_rejects_empty :
    ¬ ∀ (t : LocalTime), (fun (_ : LocalTime) => "") t = t.text := by
  intro h
  exact empty_ne_localTime_text _ (h default)

theorem localDateTime_text_rejects_empty :
    ¬ ∀ (dt : LocalDateTime), (fun (_ : LocalDateTime) => "") dt = dt.text := by
  intro h
  exact empty_ne_append (empty_ne_append (empty_ne_localDate_text _)) (h default)

theorem offsetDateTime_text_rejects_empty :
    ¬ ∀ (dt : OffsetDateTime), (fun (_ : OffsetDateTime) => "") dt = dt.text := by
  intro h
  exact empty_ne_append (empty_ne_append (empty_ne_append (empty_ne_localDate_text _))) (h default)

theorem dateTime_text_rejects_empty :
    ¬ ∀ (d : DateTime), (fun (_ : DateTime) => "") d = d.text := by
  intro h
  exact empty_ne_localDate_text _ (h (.localDate default))

theorem dateTime_parse_rejects_none :
    ¬ ∀ (s : String) (d : DateTime), (fun (_ : String) => (none : Option DateTime)) s = some d ↔ d.text = s := by
  intro h
  cases (h (DateTime.localDate default).text (.localDate default)).mpr rfl

theorem codec_localDate_rejects_null :
    ¬ ∀ (d : LocalDate), @toValue LocalDate ⟨fun _ => .null⟩ d = .string ((fun (_ : LocalDate) => "") d) ∧
      ∀ w : Value, @fromValue? LocalDate ⟨fun _ => .error ""⟩ w = .ok d ↔ w = .string d.text := by
  intro h
  nomatch (h default).1

theorem codec_localTime_rejects_null :
    ¬ ∀ (t : LocalTime), @toValue LocalTime ⟨fun _ => .null⟩ t = .string ((fun (_ : LocalTime) => "") t) ∧
      ∀ w : Value, @fromValue? LocalTime ⟨fun _ => .error ""⟩ w = .ok t ↔ w = .string t.text := by
  intro h
  nomatch (h default).1

theorem codec_localDateTime_rejects_null :
    ¬ ∀ (dt : LocalDateTime), @toValue LocalDateTime ⟨fun _ => .null⟩ dt = .string ((fun (_ : LocalDateTime) => "") dt) ∧
      ∀ w : Value, @fromValue? LocalDateTime ⟨fun _ => .error ""⟩ w = .ok dt ↔ w = .string dt.text := by
  intro h
  nomatch (h default).1

theorem codec_offsetDateTime_rejects_null :
    ¬ ∀ (dt : OffsetDateTime), @toValue OffsetDateTime ⟨fun _ => .null⟩ dt = .string ((fun (_ : OffsetDateTime) => "") dt) ∧
      ∀ w : Value, @fromValue? OffsetDateTime ⟨fun _ => .error ""⟩ w = .ok dt ↔ w = .string dt.text := by
  intro h
  nomatch (h default).1

theorem codec_dateTime_rejects_null :
    ¬ ∀ (d : DateTime), @toValue DateTime ⟨fun _ => .null⟩ d = .string ((fun (_ : DateTime) => "") d) ∧
      ∀ w : Value, @fromValue? DateTime ⟨fun _ => .error ""⟩ w = .ok d ↔ w = .string d.text := by
  intro h
  nomatch (h default).1

end ExactJSON
