module

public import ExactJSON.LeanJson
public import ExactJSON.OfScientific
public import Std.Data.TreeMap.Raw.Lemmas
public import Std.Data.TreeMap.Raw.WF
import all Lean.Data.Json.Basic

public section

namespace ExactJSON

theorem floatToJson_nonfinite (x : Float) (hx : finiteFloat x = false) :
    floatToJson x = .str (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity") := by
  simp [floatToJson, FloatText.shortest, hx]

theorem itemsToJson_eq (acc : Array Lean.Json) (items : List Value) :
    Value.itemsToJson acc items = acc ++ (items.map Value.toJson).toArray := by
  induction items generalizing acc with
  | nil => simp [Value.itemsToJson]
  | cons v rest ih => simp [Value.itemsToJson, ih]

theorem membersToJson_eq (acc : Array (String × Lean.Json)) (members : List (String × Value)) :
    Value.membersToJson acc members = acc ++ (members.map fun p => (p.1, p.2.toJson)).toArray := by
  induction members generalizing acc with
  | nil => simp [Value.membersToJson]
  | cons m rest ih => simp [Value.membersToJson, ih]

theorem toJson_array (items : List Value) :
    (Value.array ⟨items⟩).toJson = .arr (items.map Value.toJson).toArray := by
  simp [Value.toJson, itemsToJson_eq]

theorem toJson_table (members : List (String × Value)) :
    (Value.table ⟨members⟩).toJson = Lean.Json.mkObj (members.map fun p => (p.1, p.2.toJson)) := by
  simp [Value.toJson, membersToJson_eq]

theorem toJson_eq (v : Value) :
    v.toJson = match v with
      | .null => .null
      | .string s => .str s
      | .integer n => .num ⟨n, 0⟩
      | .float x => floatToJson x
      | .boolean b => .bool b
      | .array items => .arr (items.map Value.toJson)
      | .table members => Lean.Json.mkObj (members.toList.map fun (k, w) => (k, w.toJson)) := by
  match v with
  | .null => rfl
  | .string _ => rfl
  | .integer _ => rfl
  | .float _ => rfl
  | .boolean _ => rfl
  | .array ⟨items⟩ => simp [toJson_array]
  | .table ⟨members⟩ => simp only [toJson_table]

private theorem toOption_map {α β : Type} (f : α → β) (x : Except String α) :
    (f <$> x).toOption = x.toOption.map f := by
  cases x <;> rfl

theorem itemsOfJson?_eq (acc : Array Value) (items : List Lean.Json) :
    Value.itemsOfJson? acc items =
      List.toArray <$> List.mapIdxM.go (fun i item => withContext s!"[{i}]" (Value.ofJson? item)) items acc := by
  induction items generalizing acc with
  | nil => simp [Value.itemsOfJson?, List.mapIdxM.go]
  | cons item rest ih =>
    simp only [Value.itemsOfJson?, List.mapIdxM.go, map_bind, ih]

theorem ofJson?_arr (items : Array Lean.Json) :
    Value.ofJson? (.arr items) =
      .array <$> items.mapIdxM fun i item => withContext s!"[{i}]" (Value.ofJson? item) := by
  obtain ⟨items⟩ := items
  rw [List.mapIdxM_toArray, Functor.map_map]
  show Value.array <$> Value.itemsOfJson? #[] items = _
  rw [itemsOfJson?_eq, Functor.map_map]
  rfl

theorem membersOfJson?_eq (acc : Array (String × Value))
    (t : Std.DTreeMap.Internal.Impl String (fun _ => Lean.Json)) :
    Value.membersOfJson? acc t =
      t.foldlM (fun acc k v => do return acc.push (k, ← withContext k (Value.ofJson? v))) acc := by
  induction t generalizing acc with
  | leaf => rfl
  | inner _ k v l r ihl ihr =>
    simp only [Value.membersOfJson?, Std.DTreeMap.Internal.Impl.foldlM, ihl, ihr, bind_assoc, pure_bind]

theorem ofJson?_obj (kvs : Std.TreeMap.Raw String Lean.Json compare) :
    Value.ofJson? (.obj kvs) = .table <$> kvs.foldlM (init := #[]) fun acc k v => do
      return acc.push (k, ← withContext k (Value.ofJson? v)) := by
  obtain ⟨⟨t⟩⟩ := kvs
  show Value.table <$> Value.membersOfJson? #[] t = _
  rw [membersOfJson?_eq]
  rfl

theorem itemsOfJson?_toOption (acc : Array Value) (items : List Lean.Json) :
    (Value.itemsOfJson? acc items).toOption =
      (items.mapM fun i => (Value.ofJson? i).toOption).map fun l => acc ++ l.toArray := by
  induction items generalizing acc with
  | nil => simp [Value.itemsOfJson?, Except.toOption, pure, Except.pure]
  | cons item rest ih =>
    simp only [Value.itemsOfJson?, List.mapM_cons]
    cases h : Value.ofJson? item with
    | error e => rfl
    | ok w =>
      show (Value.itemsOfJson? (acc.push w) rest).toOption = _
      rw [ih]
      cases List.mapM (fun i => (Value.ofJson? i).toOption) rest with
      | none => rfl
      | some l =>
        show some (acc.push w ++ l.toArray) = some (acc ++ (w :: l).toArray)
        simp

private theorem foldlM_members_toOption (acc : Array (String × Value)) (l : List (String × Lean.Json)) :
    (l.foldlM (fun (a : Array (String × Value)) (b : String × Lean.Json) => do
      return a.push (b.1, ← withContext b.1 (Value.ofJson? b.2))) acc).toOption =
      (l.mapM fun p => (Value.ofJson? p.2).toOption.map (p.1, ·)).map fun ms => acc ++ ms.toArray := by
  induction l generalizing acc with
  | nil => simp [Except.toOption, pure, Except.pure]
  | cons p rest ih =>
    simp only [List.foldlM_cons, List.mapM_cons]
    cases h : Value.ofJson? p.2 with
    | error e => rfl
    | ok w =>
      show Except.toOption (List.foldlM (m := Except String) _ (acc.push (p.1, w)) rest) = _
      rw [ih]
      cases List.mapM (fun p => (Value.ofJson? p.2).toOption.map (p.1, ·)) rest with
      | none => rfl
      | some l =>
        show some (acc.push (p.1, w) ++ l.toArray) = some (acc ++ ((p.1, w) :: l).toArray)
        simp

theorem ofJson_eq (j : Lean.Json) :
    (Value.ofJson? j).toOption = match j with
      | .null => some .null
      | .bool b => some (.boolean b)
      | .str s => some (.string s)
      | .num n =>
        if n.exponent = 0 then some (.integer n.mantissa)
        else (Rfc8259.floatOf? (decide (n.mantissa < 0)) n.mantissa.natAbs (-(n.exponent : Int))).map .float
      | .arr items => (items.toList.mapM fun i => (Value.ofJson? i).toOption).map fun (l : List Value) => .array l.toArray
      | .obj kvs =>
        ((kvs.toList : List (String × Lean.Json)).mapM fun (p : String × Lean.Json) => (Value.ofJson? p.2).toOption.map (p.1, ·)).map
          fun (l : List (String × Value)) => .table l.toArray := by
  match j with
  | .null => rfl
  | .bool _ => rfl
  | .str _ => rfl
  | .num n =>
    by_cases h : n.exponent = 0
    · simp [Value.ofJson?, h, Except.toOption, pure, Except.pure]
    · simp only [Value.ofJson?, h, beq_iff_eq, ite_false, FloatText.ofDecimal?]
      cases Rfc8259.floatOf? (decide (n.mantissa < 0)) n.mantissa.natAbs (-(n.exponent : Int)) <;> rfl
  | .arr ⟨items⟩ =>
    show (Value.array <$> Value.itemsOfJson? #[] items).toOption = _
    rw [toOption_map, itemsOfJson?_toOption]
    simp [Option.map_map, Function.comp_def]
  | .obj kvs =>
    rw [ofJson?_obj, toOption_map, Std.TreeMap.Raw.foldlM_eq_foldlM_toList, foldlM_members_toOption]
    simp [Option.map_map, Function.comp_def]

private theorem floatOf?_of_roundsTo {x : Float} (hx : finiteFloat x = true) {neg : Bool} {M : Nat} {e : Int}
    (hd : FloatText.decompose x = (neg, M, e)) (hM : M ≠ 0) {m : Nat} {q : Int}
    (hfit : FloatText.roundsTo M e m q = true) : Rfc8259.floatOf? neg m q = some x := by
  obtain ⟨-, hr⟩ := FloatText.decompose_spec x hx neg M e hd
  obtain ⟨hr1, hr2⟩ := hr hM
  obtain ⟨hm0, hc1, hc2⟩ := FloatText.interval_bounds M e hM hr1 hr2 _ _ _ _ hfit
  rw [floatOf?_eq _ _ _ hm0 hc1 hc2]
  cases neg
  · have := ofScientificRounds x M e _ _ hx hd hM hfit
    simp only [Bool.false_eq_true, ite_false, this, hx, ite_true]
  · have := ofScientificRounds (-x) M e _ _ (FloatText.finiteFloat_neg hx)
      (by rw [FloatText.decompose_neg hx hd]; rfl) hM hfit
    simp only [ite_true, this, FloatText.neg_neg_of_finite hx, hx]

theorem ofJson?_num {n : Lean.JsonNumber} (hn : n.exponent ≠ 0) {x : Float}
    (h : Rfc8259.floatOf? (decide (n.mantissa < 0)) n.mantissa.natAbs (-(n.exponent : Int)) = some x) :
    Value.ofJson? (.num n) = .ok (.float x) := by
  simp only [Value.ofJson?, beq_iff_eq, hn, ite_false, FloatText.ofDecimal?, h]
  rfl

private theorem signed_digits (neg : Bool) (digits k : Nat) (hd : digits ≠ 0) :
    decide ((if neg then -(digits : Int) else digits) * 10 ^ k < 0) = neg ∧
      ((if neg then -(digits : Int) else digits) * 10 ^ k).natAbs = digits * 10 ^ k := by
  have hp : (0 : Int) < 10 ^ k := Int.pow_pos (by decide)
  cases neg
  · simp only [Bool.false_eq_true, ite_false, decide_eq_false_iff_not, Int.not_lt]
    exact ⟨Int.mul_nonneg (Int.natCast_nonneg _) (Int.le_of_lt hp), by rw [Int.natAbs_mul, Int.natAbs_pow]; rfl⟩
  · simp only [ite_true, decide_eq_true_eq]
    refine ⟨Int.mul_neg_of_neg_of_pos (by omega) hp, ?_⟩
    rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg]
    rfl

theorem ofJson_floatToJson (x : Float) (hx : finiteFloat x = true)
    (hz : (x.toBits != 0x8000000000000000) = true) : Value.ofJson? (floatToJson x) = .ok (.float x) := by
  rcases hd : FloatText.decompose x with ⟨neg, M, e⟩
  by_cases hM : M = 0
  · subst hM
    have hs : FloatText.shortest x = some ⟨neg, 0, 0⟩ := by
      unfold FloatText.shortest
      simp only [hx, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hd]
      rfl
    have hzero := FloatText.eq_zero_of_decompose hd
    cases neg
    · simp only [Bool.false_eq_true, ite_false] at hzero
      subst hzero
      unfold floatToJson
      rw [hs]
      have h0 : Rfc8259.floatOf? (decide ((0 : Int) < 0)) (0 : Int).natAbs (-((1 : Nat) : Int)) = some 0.0 := by
        unfold Rfc8259.floatOf?
        simp only [Int.natAbs_zero, ite_true, Option.map_some, show decide ((0 : Int) < 0) = false by decide,
          Bool.false_eq_true, ite_false, show finiteFloat 0.0 = true by decide +kernel]
      exact ofJson?_num (n := ⟨0, 1⟩) Nat.one_ne_zero h0
    · simp only [ite_true] at hzero
      subst hzero
      exact absurd hz (by decide +kernel)
  · obtain ⟨dd, hs, hneg, hfit⟩ := FloatText.shortest_spec x hx neg M e hd hM
    obtain ⟨-, hr⟩ := FloatText.decompose_spec x hx neg M e hd
    obtain ⟨hr1, hr2⟩ := hr hM
    obtain ⟨hd0, -, -⟩ := FloatText.interval_bounds M e hM hr1 hr2 _ _ _ _ hfit
    unfold floatToJson
    rw [hs]
    dsimp only
    split
    · rename_i hneg'
      obtain ⟨hsign, habs⟩ := signed_digits dd.negative dd.digits 0 hd0
      simp only [Int.pow_zero, Int.mul_one, Nat.pow_zero, Nat.mul_one] at hsign habs
      apply ofJson?_num (show (-dd.exponent).toNat ≠ 0 by omega)
      rw [hsign, habs, hneg, show -(((-dd.exponent).toNat : Nat) : Int) = dd.exponent by omega]
      exact floatOf?_of_roundsTo hx hd hM hfit
    · rename_i hpos
      obtain ⟨hsign, habs⟩ := signed_digits dd.negative dd.digits (dd.exponent.toNat + 1) hd0
      apply ofJson?_num Nat.one_ne_zero
      rw [hsign, habs, hneg]
      have hfit' : FloatText.roundsTo M e (dd.digits * 10 ^ (dd.exponent.toNat + 1)) (-((1 : Nat) : Int)) = true := by
        unfold FloatText.roundsTo
        rw [FloatText.fits_scale, show -((1 : Nat) : Int) + ((dd.exponent.toNat + 1 : Nat) : Int) = dd.exponent by omega]
        exact hfit
      exact floatOf?_of_roundsTo hx hd hM hfit'

private theorem keysIncreaseFrom_pairwise : ∀ (previous : String) (ks : List String),
    keysIncreaseFrom previous ks = true → (previous :: ks).Pairwise (fun a b => compare a b = .lt)
  | _, [], _ => List.pairwise_singleton _ _
  | previous, k :: rest, h => by
    simp only [keysIncreaseFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := keysIncreaseFrom_pairwise k rest h.2
    have first : compare previous k = .lt := Std.compare_eq_lt.mpr h.1
    refine List.Pairwise.cons (fun a ha => ?_) ih
    rcases List.mem_cons.mp ha with rfl | ha
    · exact first
    · exact Std.TransCmp.lt_trans first (List.rel_of_pairwise_cons ih ha)

private theorem keysIncrease_pairwise (ks : List String) (h : keysIncrease ks = true) :
    ks.Pairwise (fun a b => compare a b = .lt) := by
  cases ks with
  | nil => exact List.Pairwise.nil
  | cons k rest => exact keysIncreaseFrom_pairwise k rest h

private theorem toList_ofList_of_sorted (l : List (String × Lean.Json))
    (hl : l.Pairwise (fun a b => compare a.1 b.1 = .lt)) : (Std.TreeMap.Raw.ofList l compare).toList = l := by
  have hwf : (Std.TreeMap.Raw.ofList l compare).WF := Std.TreeMap.Raw.WF.ofList
  have hsorted := Std.TreeMap.Raw.ordered_keys_toList hwf
  have hdistinct : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    hl.imp fun h => by rw [h]; decide
  have nodup : ∀ {l' : List (String × Lean.Json)}, l'.Pairwise (fun a b => compare a.1 b.1 = .lt) → l'.Nodup :=
    fun h => h.imp fun hab heq => by
      subst heq
      rw [Std.ReflCmp.compare_self (cmp := (compare : String → String → Ordering))] at hab
      cases hab
  apply List.Perm.eq_of_pairwise (le := fun a b => compare a.1 b.1 = .lt) _ hsorted hl
  · rw [List.perm_ext_iff_of_nodup (nodup hsorted) (nodup hl)]
    intro ⟨k, v⟩
    rw [Std.TreeMap.Raw.mem_toList_iff_getElem?_eq_some hwf]
    constructor
    · intro h
      cases hc : (l.map Prod.fst).contains k with
      | false =>
        rw [Std.TreeMap.Raw.getElem?_ofList_of_contains_eq_false hc] at h
        cases h
      | true =>
        obtain ⟨⟨k', v'⟩, hmem, hk⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
        simp only at hk
        subst hk
        rw [Std.TreeMap.Raw.getElem?_ofList_of_mem Std.ReflCmp.compare_self hdistinct hmem] at h
        cases h
        exact hmem
    · intro h
      exact Std.TreeMap.Raw.getElem?_ofList_of_mem Std.ReflCmp.compare_self hdistinct h
  · intro a b _ _ hab hba
    rw [Std.OrientedCmp.gt_of_lt hab] at hba
    cases hba

theorem membersToJson_sorted (members : List (String × Value)) (h : keysIncrease (members.map (·.1)) = true) :
    (members.map fun p => (p.1, p.2.toJson)).Pairwise (fun a b => compare a.1 b.1 = .lt) := by
  have := keysIncrease_pairwise _ h
  rw [List.pairwise_map] at this ⊢
  exact this

mutual

theorem ofJson_toJson_of : (v : Value) → v.isValid = true → v.noNegativeZero = true →
    Value.ofJson? v.toJson = .ok v
  | .null, _, _ => rfl
  | .string _, _, _ => rfl
  | .integer _, _, _ => rfl
  | .float x, h, hz => ofJson_floatToJson x h hz
  | .boolean _, _, _ => rfl
  | .array ⟨items⟩, h, hz => by
    rw [toJson_array]
    show Value.array <$> Value.itemsOfJson? #[] (items.map Value.toJson) = _
    rw [itemsOfJson?_toJson items h hz #[]]
    simp only [Array.empty_append]
    rfl
  | .table ⟨members⟩, h, hz => by
    simp only [Value.isValid, Bool.and_eq_true] at h
    rw [toJson_table]
    show Value.ofJson? (.obj (Std.TreeMap.Raw.ofList (members.map fun p => (p.1, p.2.toJson)))) = _
    rw [ofJson?_obj, Std.TreeMap.Raw.foldlM_eq_foldlM_toList,
      toList_ofList_of_sorted _ (membersToJson_sorted members h.1), membersFold_toJson members h.2 hz #[]]
    simp only [Array.empty_append]
    rfl

theorem itemsOfJson?_toJson : (items : List Value) → itemsValid items = true →
    itemsNoNegativeZero items = true → ∀ acc : Array Value,
      Value.itemsOfJson? acc (items.map Value.toJson) = .ok (acc ++ items.toArray)
  | [], _, _, acc => by simp [Value.itemsOfJson?, pure, Except.pure]
  | v :: rest, h, hz, acc => by
    simp only [itemsValid, Bool.and_eq_true] at h
    simp only [itemsNoNegativeZero, Bool.and_eq_true] at hz
    simp only [List.map_cons, Value.itemsOfJson?, ofJson_toJson_of v h.1 hz.1]
    show Value.itemsOfJson? (acc.push v) (rest.map Value.toJson) = _
    rw [itemsOfJson?_toJson rest h.2 hz.2]
    simp

theorem membersFold_toJson : (members : List (String × Value)) → membersValid members = true →
    membersNoNegativeZero members = true → ∀ acc : Array (String × Value),
      (members.map fun p => (p.1, p.2.toJson)).foldlM (fun (a : Array (String × Value)) (b : String × Lean.Json) => do
        return a.push (b.1, ← withContext b.1 (Value.ofJson? b.2))) acc = .ok (acc ++ members.toArray)
  | [], _, _, acc => by simp [pure, Except.pure]
  | (k, v) :: rest, h, hz, acc => by
    simp only [membersValid, Bool.and_eq_true] at h
    simp only [membersNoNegativeZero, Bool.and_eq_true] at hz
    simp only [List.map_cons, List.foldlM_cons, ofJson_toJson_of v h.1 hz.1]
    show List.foldlM (m := Except String) _ (acc.push (k, v)) (rest.map fun p => (p.1, p.2.toJson)) = _
    rw [membersFold_toJson rest h.2 hz.2]
    simp

end

theorem ofJson_toJson (v : Value) (h : v.Valid) (hz : v.noNegativeZero = true) : Value.ofJson? v.toJson = .ok v :=
  ofJson_toJson_of v h hz

theorem exactToJsonFloat_eq (x : Float) : ExactFloat.exactToJsonFloat.toJson x = floatToJson x := rfl

private theorem zero_isShortest : (⟨false, 0, 0⟩ : Decimal).IsShortest 0.0 := by
  refine ⟨?_, fun _ => rfl, fun d' _ => ?_⟩
  · show Rfc8259.floatOf? false 0 0 = some 0.0
    unfold Rfc8259.floatOf?
    simp only [ite_true, Option.map_some, Bool.false_eq_true, ite_false, show finiteFloat 0.0 = true by decide +kernel]
  · have hv : (⟨false, 0, 0⟩ : Decimal).value - floatValue 0.0 = 0 := by decide +kernel
    have hc : (⟨false, 0, 0⟩ : Decimal).digitCount = 1 := by
      unfold Decimal.digitCount
      rw [Nat.toDigits_zero]
      rfl
    rw [hc, hv, Rat.abs_zero]
    rcases Nat.lt_or_ge 1 d'.digitCount with hlt | hle
    · exact Or.inl hlt
    · have hpos : 0 < d'.digitCount := List.length_pos_iff.mpr Nat.toDigits_ne_nil
      refine Or.inr ⟨by omega, ?_⟩
      rcases Rat.le_iff_lt_or_eq.mp (Rat.abs_nonneg (x := d'.value - floatValue 0.0)) with hlt | heq
      · exact Or.inl hlt
      · exact Or.inr ⟨heq, Or.inr rfl⟩

theorem floatToJson_finite_rejects_null :
    ¬ ∀ (x : Float) (d : Decimal), d.IsShortest x → (fun (_ : Float) => Lean.Json.null) x = .num d.toJsonNumber := by
  intro h
  cases h 0.0 ⟨false, 0, 0⟩ zero_isShortest

theorem floatToJson_nonfinite_rejects_null :
    ¬ ∀ (x : Float), finiteFloat x = false →
      (fun (_ : Float) => Lean.Json.null) x = .str (if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity") := by
  intro h
  cases h Float.nan (by decide +kernel)

theorem toJson_eq_rejects_null :
    ¬ ∀ (v : Value),
      (fun (_ : Value) => Lean.Json.null) v = match v with
        | .null => .null
        | .string s => .str s
        | .integer n => .num ⟨n, 0⟩
        | .float x => (fun (_ : Float) => Lean.Json.null) x
        | .boolean b => .bool b
        | .array items => .arr (items.map (fun (_ : Value) => Lean.Json.null))
        | .table members => Lean.Json.mkObj (members.toList.map fun (k, w) => (k, (fun (_ : Value) => Lean.Json.null) w)) := by
  intro h
  cases h (.boolean true)

theorem ofJson_eq_rejects_error :
    ¬ ∀ (j : Lean.Json),
      ((fun (_ : Lean.Json) => (Except.error "" : Except String Value)) j).toOption = match j with
        | .null => some .null
        | .bool b => some (.boolean b)
        | .str s => some (.string s)
        | .num n =>
          if n.exponent = 0 then some (.integer n.mantissa)
          else (Rfc8259.floatOf? (decide (n.mantissa < 0)) n.mantissa.natAbs (-(n.exponent : Int))).map .float
        | .arr items =>
          (items.toList.mapM fun i => ((fun (_ : Lean.Json) => (Except.error "" : Except String Value)) i).toOption).map
            fun (l : List Value) => .array l.toArray
        | .obj kvs =>
          ((kvs.toList : List (String × Lean.Json)).mapM fun (p : String × Lean.Json) =>
            ((fun (_ : Lean.Json) => (Except.error "" : Except String Value)) p.2).toOption.map (p.1, ·)).map
              fun (l : List (String × Value)) => .table l.toArray := by
  intro h
  cases h .null

theorem ofJson_toJson_rejects_error :
    ¬ ∀ (v : Value), v.Valid → v.noNegativeZero = true →
      (fun (_ : Lean.Json) => (Except.error "" : Except String Value)) ((fun (_ : Value) => Lean.Json.null) v) = .ok v := by
  intro h
  cases h .null rfl rfl

theorem exactToJsonFloat_eq_rejects_null :
    ¬ ∀ (x : Float), (⟨fun _ => Lean.Json.null⟩ : Lean.ToJson Float).toJson x = (fun (_ : Float) => Lean.Json.str "") x := by
  intro h
  cases h 0.0

end ExactJSON
