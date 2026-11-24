module

public import ExactJSON.Shortest
public import ExactJSON.FloatBits
public import ExactJSON.Fixed

/-! # A float's canonical text is read back as its decimal

`Rfc8259.numberValue` reads the canonical text of a decimal `D × 10^X` (`Decimal.toFloatText`) as
the float that `Rfc8259.floatOf?` makes of the same decimal, written `(D × 10^j) × 10^(X - j)`.
With `shortest_spec`, this reduces `FloatsReadBack` to one property of Lean's `Float.ofScientific`,
`OfScientificRounds`: it reads every decimal in the rounding interval of a positive finite float as
that float (it rounds to nearest, ties to even). `floatsReadBack` derives `FloatsReadBack` from it,
and with it the two headlines `read_render` and `decode_encode` (`read_render_of_rounds`,
`decode_encode_of_rounds`).
-/

public section

namespace ExactJSON

universe u

/-- What `numberValue` makes of a float's sign, digits and decimal exponent. -/
def floatResult (negative : Bool) (m : Nat) (q : Int) : Except String Value :=
  match Rfc8259.floatOf? negative m q with
  | some x => .ok (.float x)
  | none => .error "a float beyond the range of binary64"

theorem span_digits (text rest : List Char) (htext : ∀ c ∈ text, c.isDigit = true)
    (hrest : ∀ c t, rest = c :: t → c.isDigit = false) : (text ++ rest).span Char.isDigit = (text, rest) := by
  have := span_loop_text Char.isDigit text rest [] htext hrest
  simpa [List.span] using this

theorem digitsValueUpTo_eq (b : Nat) (ds : List Char) :
    Rfc8259.digitsValueUpTo b ds = min (Rfc8259.digitsValue ds) b := by
  unfold Rfc8259.digitsValueUpTo Rfc8259.digitsValue
  rw [Nat.ofDigitChars_eq_foldl, show '0'.toNat = 48 from rfl]
  have key : ∀ (a : Nat) (ds : List Char),
      ds.foldl (fun n d => min (10 * n + (d.toNat - 48)) b) (min a b) =
        min (ds.foldl (fun sofar c => 10 * sofar + (c.toNat - 48)) a) b := by
    intro a ds
    induction ds generalizing a with
    | nil => rfl
    | cons d ds ih =>
      simp only [List.foldl_cons]
      rw [← ih (10 * a + (d.toNat - 48))]
      congr 1
      omega
  have := key 0 ds
  simpa using this

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

theorem dot_not_digit : ∀ c t, ('.' :: t : List Char) = c :: t → c.isDigit = false := by
  intro c t h
  cases h
  rfl

theorem numberValue_fixed (neg : Bool) (whole frac : List Char)
    (hw : whole ≠ []) (hwd : ∀ c ∈ whole, c.isDigit = true) (hw0 : ¬(whole.head? = some '0' ∧ whole.length > 1))
    (hf : frac ≠ []) (hfd : ∀ c ∈ frac, c.isDigit = true) :
    Rfc8259.numberValue ((if neg then ['-'] else []) ++ (whole ++ '.' :: frac)) =
      floatResult neg (Rfc8259.digitsValue (whole ++ frac)) (-(frac.length : Int)) := by
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
  simp only [floatResult, List.cons_append, List.length_cons, Option.getD_some, Option.getD_none]
  rw [show (0 : Int) - ((fs.length + 1 : Nat) : Int) = -((fs.length + 1 : Nat) : Int) by omega]
  generalize Rfc8259.floatOf? _ _ _ = r
  cases r <;> rfl

theorem numberValue_sci (neg : Bool) (whole frac : List Char) (s : Int)
    (hw : whole ≠ []) (hwd : ∀ c ∈ whole, c.isDigit = true) (hw0 : ¬(whole.head? = some '0' ∧ whole.length > 1))
    (hf : frac ≠ []) (hfd : ∀ c ∈ frac, c.isDigit = true) (hs : s.natAbs < 400) :
    Rfc8259.numberValue ((if neg then ['-'] else []) ++ (whole ++ '.' :: (frac ++ 'e' :: (toString s).toList))) =
      floatResult neg (Rfc8259.digitsValue (whole ++ frac)) (s - frac.length) := by
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
  rw [← hds, digitsValueUpTo_eq, show Rfc8259.digitsValue (Nat.toDigits 10 s.natAbs) = s.natAbs from
    Nat.ofDigitChars_ten_toDigits, Nat.min_eq_left (by omega)]
  have hsv : (if decide (s < 0) = true then -(s.natAbs : Int) else (s.natAbs : Int)) = s := by
    by_cases h : s < 0 <;> simp [h] <;> omega
  simp only [hsv, Option.getD_some, floatResult, List.length_cons]
  generalize Rfc8259.floatOf? _ _ _ = r
  cases r <;> rfl

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

/-- `numberValue` reads the canonical text of a nonzero decimal as `floatOf?` makes the same
decimal, written with `j` more zeros. -/
theorem numberValue_toFloatText (d : Decimal) (hd : d.digits ≠ 0)
    (hs : (d.exponent + ((Nat.toDigits 10 d.digits).length : Int) - 1).natAbs < 400) :
    ∃ j : Nat, Rfc8259.numberValue d.toFloatText.toList =
      floatResult d.negative (d.digits * 10 ^ j) (d.exponent - j) := by
  have hdig : ∀ c ∈ Nat.toDigits 10 d.digits, c.isDigit = true := fun c h =>
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  have hhead := toDigits_head?_ne_zero d.digits (Nat.pos_of_ne_zero hd)
  have hval : Rfc8259.digitsValue (Nat.toDigits 10 d.digits) = d.digits := Nat.ofDigitChars_ten_toDigits
  have hne := Nat.toDigits_ne_nil (n := d.digits) (b := 10)
  unfold Decimal.toFloatText
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
    · -- digits, zeros, and `.0`
      simp only [h2, ite_true]
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
      · -- digits with the point inside
        simp only [h3, ite_true]
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
      · -- `0.`, zeros, digits
        simp only [h3, ite_false]
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
  · -- scientific
    simp only [h1, ite_false]
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
        (by simp) hs
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
        (fun c hc => hdig c (by simp [hc])) hs
      rw [show [c0] ++ ['.'] ++ ds' ++ ['e'] ++ (toString sci).toList =
          [c0] ++ '.' :: (ds' ++ 'e' :: (toString sci).toList) by simp, h, List.singleton_append, hval]
      simp only [Nat.pow_zero, Nat.mul_one]
      congr 1
      simp only [List.length_cons] at hn
      omega

/-! ## Every finite float reads back, if `Float.ofScientific` rounds to nearest -/

open FloatText

/-- `floatOf?` of a nonzero decimal whose exponent is in range is `Float.ofScientific`'s float,
with its sign, when that is finite. -/
theorem floatOf?_eq (neg : Bool) (m : Nat) (q : Int) (hm : m ≠ 0)
    (h1 : -324 ≤ ((Nat.toDigits 10 m).length : Int) + q) (h2 : ((Nat.toDigits 10 m).length : Int) + q ≤ 309) :
    Rfc8259.floatOf? neg m q =
      let y := if neg then -Float.ofScientific m (decide (q < 0)) q.natAbs else Float.ofScientific m (decide (q < 0)) q.natAbs
      if finiteFloat y then some y else none := by
  unfold Rfc8259.floatOf?
  simp only [hm, ite_false, show ¬ (((Nat.toDigits 10 m).length : Int) + q > 309) by omega,
    show ¬ (((Nat.toDigits 10 m).length : Int) + q < -324) by omega, Option.map]

/-- Whether the decimal `m × 10^q` rounds to the positive float `M × 2^e` (the significand and
binary exponent `decompose` gives): whether it lies in the interval of reals that round to it, to
nearest with ties to an even significand. -/
@[expose] def FloatText.roundsTo (M : Nat) (e : Int) (m : Nat) (q : Int) : Bool :=
  let lowerCloser := decide (M = 2 ^ 52) && decide (e > -1074)
  FloatText.fits (FloatText.roundingInterval M lowerCloser).1 (FloatText.roundingInterval M lowerCloser).2.2
    (FloatText.scale e q).1 (FloatText.scale e q).2 (M % 2 == 0) m


/-- Lean's `Float.ofScientific` rounds to nearest, ties to even: it reads every decimal in the
rounding interval of a positive finite float as that float. -/
@[expose] def OfScientificRounds : Prop :=
  ∀ (x : Float) (M : Nat) (e : Int) (m : Nat) (q : Int), finiteFloat x = true →
    FloatText.decompose x = (false, M, e) → M ≠ 0 → FloatText.roundsTo M e m q = true →
    Float.ofScientific m (decide (q < 0)) q.natAbs = x

/-- A float is read back when its text reads as a decimal that `floatOf?` makes it. -/
theorem rereadFloat_of_numberValue {x : Float} {neg : Bool} {m : Nat} {q : Int}
    (h : Rfc8259.numberValue (floatText x).toList = floatResult neg m q) (hf : Rfc8259.floatOf? neg m q = some x) :
    Value.rereadFloat x = some (.float x) := by
  unfold Value.rereadFloat
  rw [h]
  unfold floatResult
  rw [hf]

/-- The text of a finite float is the text of its shortest decimal. -/
theorem floatText_of_shortest {x : Float} {dd : Decimal} (h : shortest x = some dd) :
    floatText x = dd.toFloatText := by
  unfold floatText Float.toCanonical?
  rw [h]
  rfl

/-- Every finite float is read back from its canonical text, if `Float.ofScientific` rounds to
nearest. -/
theorem floatsReadBack (rounds : OfScientificRounds) : FloatsReadBack := by
  intro x hx
  rcases hd : decompose x with ⟨neg, M, e⟩
  by_cases hM : M = 0
  · subst hM
    have hz := eq_zero_of_decompose hd
    have hs : shortest x = some ⟨neg, 0, 0⟩ := by
      unfold shortest
      simp only [hx, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hd]
      rfl
    have hread := numberValue_fixed neg ['0'] ['0'] (by simp) (by decide) (by decide) (by simp) (by decide)
    apply rereadFloat_of_numberValue (neg := neg) (m := Rfc8259.digitsValue (['0'] ++ ['0'])) (q := -1)
    · rw [floatText_of_shortest hs]
      unfold Decimal.toFloatText
      simp only [ite_true]
      rw [String.toList_ofList]
      exact hread
    · have h00 : Rfc8259.digitsValue (['0'] ++ ['0']) = 0 := by
        rw [show (['0'] ++ ['0'] : List Char) = List.replicate 2 '0' by simp [List.replicate]]
        unfold Rfc8259.digitsValue
        rw [Nat.ofDigitChars_replicate_zero]
      rw [hz]
      unfold Rfc8259.floatOf?
      simp only [h00, ite_true, Option.map]
      cases neg
      · simp only [Bool.false_eq_true, ite_false]
        rw [show finiteFloat 0.0 = true by decide +kernel]
        rfl
      · simp only [ite_true]
        rw [show finiteFloat (-0.0) = true by decide +kernel]
        rfl
  · obtain ⟨-, hr⟩ := decompose_spec x hx neg M e hd
    obtain ⟨hr1, hr2⟩ := hr hM
    obtain ⟨dd, hs, hneg, hfit⟩ := shortest_spec x hx neg M e hd hM
    obtain ⟨hd0, hb1, hb2⟩ := interval_bounds M e hM hr1 hr2 _ _ _ _ hfit
    obtain ⟨j, hj⟩ := numberValue_toFloatText dd hd0 (by omega)
    have hfit' : fits (roundingInterval M (decide (M = 2 ^ 52) && decide (e > -1074))).1
        (roundingInterval M (decide (M = 2 ^ 52) && decide (e > -1074))).2.2
        (scale e (dd.exponent - j)).1 (scale e (dd.exponent - j)).2 (M % 2 == 0) (dd.digits * 10 ^ j) = true := by
      rw [fits_scale, show dd.exponent - j + j = dd.exponent by omega]
      exact hfit
    obtain ⟨hm0, hc1, hc2⟩ := interval_bounds M e hM hr1 hr2 _ _ _ _ hfit'
    have hround : roundsTo M e (dd.digits * 10 ^ j) (dd.exponent - j) = true := hfit'
    rw [← floatText_of_shortest hs] at hj
    apply rereadFloat_of_numberValue hj
    rw [floatOf?_eq _ _ _ hm0 hc1 hc2, hneg]
    cases neg
    · have := rounds x M e _ _ hx hd hM hround
      simp only [Bool.false_eq_true, ite_false, this, hx, ite_true]
    · have := rounds (-x) M e _ _ (finiteFloat_neg hx) (by rw [decompose_neg hx hd]; rfl) hM hround
      simp only [ite_true, this, neg_neg_of_finite hx, hx]

/-- `read_render`, if `Float.ofScientific` rounds to nearest. -/
theorem read_render_of_rounds (rounds : OfScientificRounds) (v : Value) (h : v.Valid) :
    Rfc8259.read? v.render = some v :=
  read_render_of_floats (floatsReadBack rounds) v h

/-- `decode_encode`, if `Float.ofScientific` rounds to nearest. -/
theorem decode_encode_of_rounds (rounds : OfScientificRounds) {α : Type u} [ToValue α] [FromValue α]
    (lawful : ∀ a : α, fromValue? (toValue a) = .ok a) (valid : ∀ a : α, (toValue a).Valid) (a : α) :
    decode (encode a) = .ok a :=
  decode_encode_of_floats (floatsReadBack rounds) lawful valid a

end ExactJSON
