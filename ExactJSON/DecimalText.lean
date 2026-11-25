module

public import ExactJSON.NumberText
public import ExactJSON.Normalize

public section

namespace ExactJSON

def decimalResult (negative : Bool) (m : Nat) (q : Int) : Except String Value :=
  .ok (.decimal (Decimal.normalize negative m q))

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

theorem span_digits (text rest : List Char) (htext : ∀ c ∈ text, c.isDigit = true)
    (hrest : ∀ c t, rest = c :: t → c.isDigit = false) : (text ++ rest).span Char.isDigit = (text, rest) := by
  have := span_loop_text Char.isDigit text rest [] htext hrest
  simpa [List.span] using this

theorem intToString_toList (s : Int) :
    (toString s).toList = (if 0 ≤ s then [] else ['-']) ++ Nat.toDigits 10 s.natAbs := by
  rw [Int.toString_eq_repr, Int.repr_eq_ite]
  split
  · rename_i h
    simp only [List.nil_append, Nat.toList_repr]
    congr 1
    omega
  · rename_i h
    simp only [String.toList_append, Nat.toList_repr]
    rw [show "-".toList = ['-'] from rfl]
    congr 2
    omega

theorem numberValue_fixed (neg : Bool) (whole frac : List Char)
    (hw : whole ≠ []) (hwd : ∀ c ∈ whole, c.isDigit = true) (hw0 : ¬(whole.head? = some '0' ∧ whole.length > 1))
    (hf : frac ≠ []) (hfd : ∀ c ∈ frac, c.isDigit = true) :
    Rfc8259.numberValue ((if neg then ['-'] else []) ++ (whole ++ '.' :: frac)) =
      decimalResult neg (Rfc8259.digitsValue (whole ++ frac)) (-(frac.length : Int)) := by
  obtain ⟨c, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  have hc : c.isDigit = true := hwd c (by simp)
  have hcm : c ≠ '-' := by rintro rfl; simp at hc
  have hspan1 := span_digits (c :: w) ('.' :: frac) hwd (fun d t h => by cases h; rfl)
  have hspan2 := span_digits frac [] hfd (fun d t h => by cases h)
  rw [List.append_nil] at hspan2
  unfold Rfc8259.numberValue
  split
  rename_i signed t sign
  have hst : signed = neg ∧ t = c :: w ++ '.' :: frac := by
    unfold Rfc8259.numberSign at sign
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append] at sign <;>
      (try split at sign) <;> simp_all
  obtain ⟨rfl, rfl⟩ := hst
  rw [hspan1]
  dsimp only
  rw [ite_eq_right (by simp), ite_eq_right (by simpa using hw0)]
  obtain ⟨f, fs, rfl⟩ := List.exists_cons_of_ne_nil hf
  simp only [hspan2, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  simp only [decimalResult, List.cons_append, List.length_cons, Option.getD_some, Option.getD_none]
  rw [show (0 : Int) - ((fs.length + 1 : Nat) : Int) = -((fs.length + 1 : Nat) : Int) by omega]
  all_goals rfl

theorem numberValue_sci (neg : Bool) (whole frac : List Char) (s : Int)
    (hw : whole ≠ []) (hwd : ∀ c ∈ whole, c.isDigit = true) (hw0 : ¬(whole.head? = some '0' ∧ whole.length > 1))
    (hf : frac ≠ []) (hfd : ∀ c ∈ frac, c.isDigit = true) :
    Rfc8259.numberValue ((if neg then ['-'] else []) ++ (whole ++ '.' :: (frac ++ 'e' :: (toString s).toList))) =
      decimalResult neg (Rfc8259.digitsValue (whole ++ frac)) (s - frac.length) := by
  obtain ⟨c, w, rfl⟩ := List.exists_cons_of_ne_nil hw
  have hc : c.isDigit = true := hwd c (by simp)
  have hcm : c ≠ '-' := by rintro rfl; simp at hc
  have hspan1 := span_digits (c :: w) ('.' :: (frac ++ 'e' :: (toString s).toList)) hwd
    (fun d t h => by cases h; rfl)
  have hspan2 := span_digits frac ('e' :: (toString s).toList) hfd (fun d t h => by cases h; rfl)
  have hdigits : ∀ c ∈ Nat.toDigits 10 s.natAbs, c.isDigit = true := fun c h =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  have hspan3 := span_digits (Nat.toDigits 10 s.natAbs) [] hdigits (fun d t h => by cases h)
  rw [List.append_nil] at hspan3
  obtain ⟨d0, ds0, hds⟩ := List.exists_cons_of_ne_nil (Nat.toDigits_ne_nil (n := s.natAbs) (b := 10))
  have hd0 : d0.isDigit = true := hdigits d0 (by rw [hds]; simp)
  have hd0m : d0 ≠ '-' := by rintro rfl; simp at hd0
  have hd0p : d0 ≠ '+' := by rintro rfl; simp at hd0
  unfold Rfc8259.numberValue
  split
  rename_i signed t sign
  have hst : signed = neg ∧ t = c :: w ++ '.' :: (frac ++ 'e' :: (toString s).toList) := by
    unfold Rfc8259.numberSign at sign
    cases neg <;> simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, List.singleton_append] at sign <;>
      (try split at sign) <;> simp_all
  obtain ⟨rfl, rfl⟩ := hst
  rw [hspan1]
  dsimp only
  rw [ite_eq_right (by simp), ite_eq_right (by simpa using hw0)]
  obtain ⟨f, fs, rfl⟩ := List.exists_cons_of_ne_nil hf
  simp only [hspan2, List.isEmpty_cons, Bool.false_eq_true, ite_false]
  simp only [BEq.rfl, Bool.true_or, ite_true]
  rw [intToString_toList]
  have hsg : Rfc8259.exponentSign ((if 0 ≤ s then [] else ['-']) ++ Nat.toDigits 10 s.natAbs) =
      (decide (s < 0), Nat.toDigits 10 s.natAbs) := by
    by_cases hs0 : 0 ≤ s
    · simp only [hs0, ite_true, List.nil_append]
      rw [hds, Rfc8259.exponentSign.eq_3 _ (fun t h => hd0m (List.cons.inj h).1)
        (fun t h => hd0p (List.cons.inj h).1)]
      simp only [Prod.mk.injEq, and_true]
      rw [eq_comm, decide_eq_false_iff_not]
      omega
    · simp only [hs0, ite_false, List.singleton_append, Rfc8259.exponentSign]
      simp only [Prod.mk.injEq, and_true]
      rw [eq_comm, decide_eq_true_eq]
      omega
  rw [hsg]
  dsimp only
  rw [hspan3, hds]
  simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false]
  rw [← hds, show Rfc8259.digitsValue (Nat.toDigits 10 s.natAbs) = s.natAbs from
    Nat.ofDigitChars_ten_toDigits]
  have hsv : (if decide (s < 0) = true then -(s.natAbs : Int) else (s.natAbs : Int)) = s := by
    by_cases h : s < 0 <;> simp [h] <;> omega
  simp only [hsv, Option.getD_some, decimalResult, List.length_cons]
  all_goals rfl

theorem digitsValue_append (l1 l2 : List Char) :
    Rfc8259.digitsValue (l1 ++ l2) = Nat.ofDigitChars 10 l2 (Rfc8259.digitsValue l1) := by
  unfold Rfc8259.digitsValue
  rw [Nat.ofDigitChars_append]

theorem digitsValue_zero_pad (ds : List Char) (z : Nat) :
    Rfc8259.digitsValue (ds ++ Decimal.zeros z) = Rfc8259.digitsValue ds * 10 ^ z := by
  rw [digitsValue_append]
  unfold Decimal.zeros
  rw [Nat.ofDigitChars_replicate_zero, Nat.mul_comm]

theorem digitsValue_leading_zeros (z : Nat) (ds : List Char) :
    Rfc8259.digitsValue ('0' :: (Decimal.zeros z ++ ds)) = Rfc8259.digitsValue ds := by
  have : '0' :: (Decimal.zeros z ++ ds) = Decimal.zeros (z + 1) ++ ds := by
    simp [Decimal.zeros, List.replicate_succ]
  rw [this, digitsValue_append]
  unfold Decimal.zeros Rfc8259.digitsValue
  rw [Nat.ofDigitChars_replicate_zero, Nat.mul_zero]

theorem zeros_digits (z : Nat) : ∀ c ∈ Decimal.zeros z, c.isDigit = true := by
  intro c h
  simp only [Decimal.zeros, List.mem_replicate] at h
  rw [h.2]
  rfl

theorem numberValue_decimalText (d : Decimal) (hd : d.digits ≠ 0) :
    ∃ j : Nat, Rfc8259.numberValue d.text.toList =
      decimalResult d.negative (d.digits * 10 ^ j) (d.exponent - j) := by
  have hs : d.exponent + ((Nat.toDigits 10 d.digits).length : Int) - 1 =
      d.exponent + ((Nat.toDigits 10 d.digits).length : Int) - 1 := rfl
  have hdig : ∀ c ∈ Nat.toDigits 10 d.digits, c.isDigit = true := fun c h =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  have hhead := toDigits_head?_ne_zero d.digits (Nat.pos_of_ne_zero hd)
  have hval : Rfc8259.digitsValue (Nat.toDigits 10 d.digits) = d.digits := Nat.ofDigitChars_ten_toDigits
  have hne := Nat.toDigits_ne_nil (n := d.digits) (b := 10)
  unfold Decimal.text
  simp only [hd, ite_false]
  rw [String.toList_ofList]
  generalize Nat.toDigits 10 d.digits = ds at hdig hhead hval hne hs
  generalize hn : ds.length = n at hs
  have hn1 : 1 ≤ n := by rw [← hn]; exact List.length_pos_iff.mpr hne
  generalize hsci : d.exponent + (n : Int) - 1 = sci at hs
  obtain ⟨c0, ds', rfl⟩ := List.exists_cons_of_ne_nil hne
  have hc0 : c0 ≠ '0' := by simpa using hhead
  by_cases h1 : -4 ≤ sci ∧ sci < 16
  · simp only [h1, and_self, ite_true]
    by_cases h2 : sci ≥ (n : Int) - 1
    · simp only [h2, ite_true]
      refine ⟨(sci - (n - 1)).toNat + 1, ?_⟩
      have h := numberValue_fixed d.negative (c0 :: ds' ++ Decimal.zeros (sci - (n - 1)).toNat) ['0']
        (by simp) (by
          intro c hc
          rcases List.mem_append.mp hc with h | h
          · exact hdig c h
          · exact zeros_digits _ c h)
        (by simp [hc0]) (by simp) (by simp)
      rw [show c0 :: ds' ++ Decimal.zeros (sci - (↑n - 1)).toNat ++ ['.', '0'] =
          c0 :: ds' ++ Decimal.zeros (sci - (↑n - 1)).toNat ++ '.' :: ['0'] by rfl, h,
        digitsValue_append, digitsValue_zero_pad, hval]
      simp only [Nat.ofDigitChars_cons, Nat.ofDigitChars_nil, List.length_cons, List.length_nil]
      rw [show '0'.toNat - '0'.toNat = 0 by rfl, Nat.add_zero, Nat.pow_succ]
      congr 1
      · ac_rfl
      · omega
    · simp only [h2, ite_false]
      by_cases h3 : 0 ≤ sci
      · simp only [h3, ite_true]
        refine ⟨0, ?_⟩
        have hkn : sci.toNat + 1 < n := by omega
        have hlen : (List.drop (sci.toNat + 1) (c0 :: ds')).length = n - (sci.toNat + 1) := by
          rw [List.length_drop, hn]
        have hfne : List.drop (sci.toNat + 1) (c0 :: ds') ≠ [] := by
          intro h
          rw [h] at hlen
          simp at hlen
          omega
        have h := numberValue_fixed d.negative (List.take (sci.toNat + 1) (c0 :: ds'))
          (List.drop (sci.toNat + 1) (c0 :: ds')) (by simp)
          (fun c hc => hdig c (List.mem_of_mem_take hc)) (by simp [hc0]) hfne
          (fun c hc => hdig c (List.mem_of_mem_drop hc))
        rw [show List.take (sci.toNat + 1) (c0 :: ds') ++ ['.'] ++ List.drop (sci.toNat + 1) (c0 :: ds') =
            List.take (sci.toNat + 1) (c0 :: ds') ++ '.' :: List.drop (sci.toNat + 1) (c0 :: ds') by simp,
          h, List.take_append_drop, hval, hlen]
        simp only [Nat.pow_zero, Nat.mul_one]
        congr 1
        omega
      · simp only [h3, ite_false]
        refine ⟨0, ?_⟩
        have h := numberValue_fixed d.negative ['0'] (Decimal.zeros ((-sci).toNat - 1) ++ c0 :: ds')
          (by simp) (by simp) (by simp) (by simp) (by
            intro c hc
            rcases List.mem_append.mp hc with h | h
            · exact zeros_digits _ c h
            · exact hdig c h)
        rw [show ['0', '.'] ++ Decimal.zeros ((-sci).toNat - 1) ++ c0 :: ds' =
            ['0'] ++ '.' :: (Decimal.zeros ((-sci).toNat - 1) ++ c0 :: ds') by simp,
          h, List.singleton_append, digitsValue_leading_zeros, hval]
        simp only [Nat.pow_zero, Nat.mul_one, List.length_append, hn]
        congr 1
        simp only [Decimal.zeros, List.length_replicate]
        omega
  · simp only [h1, ite_false]
    simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons, List.drop_zero]
    by_cases h4 : n = 1
    · simp only [h4, ite_true]
      have hds' : ds' = [] := by
        rw [← hn] at h4
        simpa using h4
      subst hds'
      refine ⟨1, ?_⟩
      have h := numberValue_sci d.negative [c0] ['0'] sci (by simp) (fun c hc => hdig c (by simp at hc; simp [hc]))
        (by simp) (by simp)
        (by simp)
      rw [show [c0] ++ ['.'] ++ ['0'] ++ ['e'] ++ (toString sci).toList =
          [c0] ++ '.' :: (['0'] ++ 'e' :: (toString sci).toList) by simp, h]
      congr 1
      · rw [← hval]
        simp [Rfc8259.digitsValue, Nat.ofDigitChars_cons]
        omega
      · simp only [List.length_singleton]
        omega
    · simp only [h4, ite_false]
      refine ⟨0, ?_⟩
      have hne' : ds' ≠ [] := by
        rintro rfl
        simp at hn
        omega
      have h := numberValue_sci d.negative [c0] ds' sci (by simp) (fun c hc => hdig c (by simp at hc; simp [hc]))
        (by simp) hne'
        (fun c hc => hdig c (by simp [hc]))
      rw [show [c0] ++ ['.'] ++ ds' ++ ['e'] ++ (toString sci).toList =
          [c0] ++ '.' :: (ds' ++ 'e' :: (toString sci).toList) by simp, h, List.singleton_append, hval]
      simp only [Nat.pow_zero, Nat.mul_one]
      congr 1
      simp only [List.length_cons] at hn
      omega

theorem numberValue_text (d : Decimal) :
    Rfc8259.numberValue d.text.toList = .ok (.decimal d) := by
  by_cases hd : d.digits = 0
  · have hz := Decimal.eq_zero d hd
    have hread := numberValue_fixed d.negative ['0'] ['0'] (by simp) (by decide) (by decide) (by simp) (by decide)
    have h00 : Rfc8259.digitsValue (['0'] ++ ['0']) = 0 := by
      rw [show (['0'] ++ ['0'] : List Char) = List.replicate 2 '0' by simp [List.replicate]]
      unfold Rfc8259.digitsValue
      rw [Nat.ofDigitChars_replicate_zero]
    unfold Decimal.text
    simp only [hd, ite_true]
    rw [String.toList_ofList]
    refine hread.trans ?_
    unfold decimalResult
    rw [h00, Decimal.normalize_zero, ← hz]
  · obtain ⟨j, hj⟩ := numberValue_decimalText d hd
    rw [hj]
    unfold decimalResult
    rw [Decimal.normalize_of_normal d hd j]

end ExactJSON
