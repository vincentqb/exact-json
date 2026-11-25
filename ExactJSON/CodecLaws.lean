module

public import ExactJSON.Codec
public import ExactJSON.FloatBits

public section

namespace ExactJSON

universe u v

private theorem pure_eq_ok {α : Type u} (a : α) : (pure a : Except String α) = .ok a := rfl

private theorem except_map_eq_ok {α β : Type u} (f : α → β) (x : Except String α) (b : β) :
    x.map f = .ok b ↔ ∃ a, x = .ok a ∧ f a = b := by
  cases x <;> simp [Except.map]

private theorem intInRange_eq_ok (lo hi : Int) (name : String) (w : Value) (m : Int) :
    Value.intInRange lo hi name w = .ok m ↔ w = .integer m ∧ lo ≤ m ∧ m ≤ hi := by
  cases w with
  | integer n =>
    simp only [Value.intInRange]
    split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      constructor
      · intro h'
        cases h'
        exact ⟨rfl, h⟩
      · rintro ⟨h1, -⟩
        cases h1
        rfl
    · rename_i h
      constructor
      · intro h'
        cases h'
      · rintro ⟨h1, h2, h3⟩
        cases h1
        simp_all
  | _ => simp [Value.intInRange, typeMismatch]

private theorem intInRange_map_eq_ok {β : Type} (lo hi : Int) (name : String) (f : Int → β) (g : β → Int)
    (hfg : ∀ m, lo ≤ m → m ≤ hi → g (f m) = m) (hgf : ∀ b, f (g b) = b) (hg : ∀ b, lo ≤ g b ∧ g b ≤ hi)
    (w : Value) (b : β) :
    (Value.intInRange lo hi name w).map f = .ok b ↔ w = .integer (g b) := by
  rw [except_map_eq_ok]
  constructor
  · rintro ⟨m, hm, rfl⟩
    obtain ⟨rfl, h0, h1⟩ := (intInRange_eq_ok lo hi name w m).mp hm
    rw [hfg m h0 h1]
  · rintro rfl
    exact ⟨g b, (intInRange_eq_ok lo hi name _ _).mpr ⟨rfl, hg b⟩, hgf b⟩

private theorem mapIdxM_go_eq_ok {α : Type u} [FromValue α] (c : Nat → String) :
    ∀ (bs : List Value) (acc : Array α) (ys : List α),
      List.mapIdxM.go (fun i v => withContext (c i) (fromValue? v)) bs acc = .ok ys ↔
        ∃ zs, bs.mapM fromValue? = .ok zs ∧ ys = acc.toList ++ zs
  | [], acc, ys => by
    simp only [List.mapIdxM.go, List.mapM_nil]
    constructor
    · intro h
      cases h
      exact ⟨[], rfl, by simp⟩
    · rintro ⟨zs, h, rfl⟩
      cases h
      simp [pure_eq_ok]
  | b :: bs, acc, ys => by
    simp only [List.mapIdxM.go, List.mapM_cons]
    cases hb : (fromValue? b : Except String α) with
    | error e =>
      constructor
      · intro h
        cases h
      · rintro ⟨zs, h, -⟩
        cases h
    | ok a =>
      have ih := mapIdxM_go_eq_ok c bs (acc.push a) ys
      simp only [withContext, Except.mapError, bind, Except.bind] at ih ⊢
      rw [ih]
      cases hbs : (List.mapM fromValue? bs : Except String (List α)) with
      | error e =>
        constructor
        · rintro ⟨zs, h, -⟩
          cases h
        · rintro ⟨zs, h, -⟩
          cases h
      | ok zs =>
        constructor
        · rintro ⟨zs', h, rfl⟩
          cases h
          exact ⟨a :: zs, rfl, by simp⟩
        · rintro ⟨zs', h, rfl⟩
          cases h
          exact ⟨zs, rfl, by simp⟩

private theorem mapIdxM_eq_ok {α : Type u} [FromValue α] (c : Nat → String) (items : Array Value) (xs : Array α) :
    items.mapIdxM (fun i v => withContext (c i) (fromValue? v)) = .ok xs ↔
      items.toList.mapM fromValue? = .ok xs.toList := by
  rcases items with ⟨l⟩
  rcases xs with ⟨xl⟩
  rw [List.mapIdxM_toArray]
  simp only [List.mapIdxM]
  cases h : List.mapIdxM.go (fun i v => withContext (c i) (fromValue? v : Except String α)) l #[] with
  | error e =>
    constructor
    · intro h'
      cases h'
    · intro h'
      have := (mapIdxM_go_eq_ok c l #[] xl).mpr ⟨xl, h', by simp⟩
      rw [h] at this
      cases this
  | ok ys =>
    have := (mapIdxM_go_eq_ok c l #[] ys).mp h
    obtain ⟨zs, hzs, rfl⟩ := this
    rw [hzs]
    constructor
    · intro h'
      cases h'
      rfl
    · intro h'
      cases h'
      rfl

private theorem fromValue_pair {α β : Type u} [FromValue α] [FromValue β] (x y : Value) :
    (fromValue? (Value.array #[x, y]) : Except String (α × β)) =
      (do let a' ← withContext "[0]" (fromValue? x); let b' ← withContext "[1]" (fromValue? y); return (a', b')) :=
  rfl

theorem codec_string (s : String) :
    toValue s = (.string s : Value) ∧ ∀ w : Value, fromValue? w = .ok s ↔ w = (.string s : Value) := by
  refine ⟨rfl, fun w => ⟨fun h => ?_, fun h => by rw [h]; rfl⟩⟩
  cases w <;> cases h <;> rfl

theorem codec_decimal (d : Decimal) :
    toValue d = (.decimal d : Value) ∧ ∀ w : Value, fromValue? w = .ok d ↔ w = (.decimal d : Value) := by
  refine ⟨rfl, fun w => ⟨fun h => ?_, fun h => by rw [h]; rfl⟩⟩
  cases w <;> cases h <;> rfl

theorem codec_bool (b : Bool) :
    toValue b = (.boolean b : Value) ∧ ∀ w : Value, fromValue? w = .ok b ↔ w = (.boolean b : Value) := by
  refine ⟨rfl, fun w => ⟨fun h => ?_, fun h => by rw [h]; rfl⟩⟩
  cases w <;> cases h <;> rfl

theorem codec_int (n : Int) :
    toValue n = (.integer n : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n : Value) := by
  refine ⟨rfl, fun w => ⟨fun h => ?_, fun h => by rw [h]; rfl⟩⟩
  cases w <;> cases h <;> rfl

theorem codec_nat (n : Nat) :
    toValue n = (.integer n : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n : Value) := by
  refine ⟨rfl, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · cases w with
    | integer m =>
      simp only [fromValue?] at h
      split at h
      · cases h
        rename_i hm
        congr 1
        omega
      · cases h
    | _ => cases h
  · rw [h]
    show (if (0 : Int) ≤ (n : Int) then pure (n : Int).toNat else typeMismatch "a natural number" (.integer n)) = _
    split
    · rfl
    · omega

theorem codec_uInt8 (n : UInt8) :
    toValue n = (.integer n.toNat : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toNat : Value) :=
  ⟨rfl, fun w => intInRange_map_eq_ok 0 (2 ^ 8 - 1) "UInt8" (·.toNat.toUInt8) (fun b => (b.toNat : Int))
    (fun m h0 h1 => by simp; omega) (fun b => by simp) (fun b => by have := b.toNat_lt; omega) w n⟩

theorem codec_uInt16 (n : UInt16) :
    toValue n = (.integer n.toNat : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toNat : Value) :=
  ⟨rfl, fun w => intInRange_map_eq_ok 0 (2 ^ 16 - 1) "UInt16" (·.toNat.toUInt16) (fun b => (b.toNat : Int))
    (fun m h0 h1 => by simp; omega) (fun b => by simp) (fun b => by have := b.toNat_lt; omega) w n⟩

theorem codec_uInt32 (n : UInt32) :
    toValue n = (.integer n.toNat : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toNat : Value) :=
  ⟨rfl, fun w => intInRange_map_eq_ok 0 (2 ^ 32 - 1) "UInt32" (·.toNat.toUInt32) (fun b => (b.toNat : Int))
    (fun m h0 h1 => by simp; omega) (fun b => by simp) (fun b => by have := b.toNat_lt; omega) w n⟩

theorem codec_uInt64 (n : UInt64) :
    toValue n = (.integer n.toNat : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toNat : Value) :=
  ⟨rfl, fun w => intInRange_map_eq_ok 0 (2 ^ 64 - 1) "UInt64" (·.toNat.toUInt64) (fun b => (b.toNat : Int))
    (fun m h0 h1 => by simp; omega) (fun b => by simp) (fun b => by have := b.toNat_lt; omega) w n⟩

theorem codec_int8 (n : Int8) :
    toValue n = (.integer n.toInt : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toInt : Value) :=
  ⟨rfl, fun w => intInRange_map_eq_ok (-2 ^ 7) (2 ^ 7 - 1) "Int8" Int8.ofInt Int8.toInt
    (fun m h0 h1 => Int8.toInt_ofInt_of_le h0 (by omega)) Int8.ofInt_toInt
    (fun b => ⟨b.le_toInt, by have := b.toInt_lt; omega⟩) w n⟩

theorem codec_int16 (n : Int16) :
    toValue n = (.integer n.toInt : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toInt : Value) :=
  ⟨rfl, fun w => intInRange_map_eq_ok (-2 ^ 15) (2 ^ 15 - 1) "Int16" Int16.ofInt Int16.toInt
    (fun m h0 h1 => Int16.toInt_ofInt_of_le h0 (by omega)) Int16.ofInt_toInt
    (fun b => ⟨b.le_toInt, by have := b.toInt_lt; omega⟩) w n⟩

theorem codec_int32 (n : Int32) :
    toValue n = (.integer n.toInt : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toInt : Value) :=
  ⟨rfl, fun w => intInRange_map_eq_ok (-2 ^ 31) (2 ^ 31 - 1) "Int32" Int32.ofInt Int32.toInt
    (fun m h0 h1 => Int32.toInt_ofInt_of_le h0 (by omega)) Int32.ofInt_toInt
    (fun b => ⟨b.le_toInt, by have := b.toInt_lt; omega⟩) w n⟩

theorem codec_int64 (n : Int64) :
    toValue n = (.integer n.toInt : Value) ∧ ∀ w : Value, fromValue? w = .ok n ↔ w = (.integer n.toInt : Value) :=
  ⟨rfl, fun w => intInRange_map_eq_ok (-2 ^ 63) (2 ^ 63 - 1) "Int64" Int64.ofInt Int64.toInt
    (fun m h0 h1 => Int64.toInt_ofInt_of_le h0 (by omega)) Int64.ofInt_toInt
    (fun b => ⟨b.le_toInt, by have := b.toInt_lt; omega⟩) w n⟩

theorem codec_char (c : Char) :
    toValue c = (.string (String.singleton c) : Value) ∧ ∀ w : Value, fromValue? w = .ok c ↔ w = (.string (String.singleton c) : Value) := by
  refine ⟨rfl, fun w => ⟨fun h => ?_, fun h => ?_⟩⟩
  · cases w with
    | string s =>
      simp only [fromValue?] at h
      split at h
      · rename_i c' hs
        cases h
        congr 1
        rw [← String.toList_inj, hs, String.toList_singleton]
      · cases h
    | _ => cases h
  · rw [h]
    simp only [fromValue?, String.toList_singleton]
    rfl

theorem codec_array {α : Type u} [ToValue α] [FromValue α] (xs : Array α) :
    toValue xs = .array (xs.map toValue) ∧
      ∀ w : Value, fromValue? w = .ok xs ↔ ∃ vs : Array Value, w = .array vs ∧ vs.toList.mapM fromValue? = .ok xs.toList := by
  refine ⟨rfl, fun w => ?_⟩
  cases w with
  | array items =>
    simp only [fromValue?]
    rw [mapIdxM_eq_ok]
    constructor
    · intro h
      exact ⟨items, rfl, h⟩
    · rintro ⟨vs, hvs, h⟩
      cases hvs
      exact h
  | _ =>
    constructor
    · intro h
      cases h
    · rintro ⟨vs, hvs, -⟩
      cases hvs

theorem codec_list {α : Type u} [ToValue α] [FromValue α] (xs : List α) :
    toValue xs = .array (xs.map toValue).toArray ∧
      ∀ w : Value, fromValue? w = .ok xs ↔ ∃ vs : Array Value, w = .array vs ∧ vs.toList.mapM fromValue? = .ok xs := by
  refine ⟨?_, fun w => ?_⟩
  · show Value.array (xs.toArray.map toValue) = _
    rw [List.map_toArray]
  · show Array.toList <$> (fromValue? w : Except String (Array α)) = .ok xs ↔ _
    constructor
    · intro h
      cases hw : (fromValue? w : Except String (Array α)) with
      | error e =>
        rw [hw] at h
        cases h
      | ok ys =>
        rw [hw] at h
        cases h
        exact ((codec_array ys).2 w).mp hw
    · rintro ⟨vs, hvs, h⟩
      have hw : (fromValue? w : Except String (Array α)) = .ok xs.toArray :=
        ((codec_array xs.toArray).2 w).mpr ⟨vs, hvs, h⟩
      rw [hw]
      rfl

theorem codec_prod {α β : Type u} [ToValue α] [ToValue β] [FromValue α] [FromValue β] (a : α) (b : β) :
    toValue (a, b) = .array #[toValue a, toValue b] ∧
      ∀ w : Value, fromValue? w = .ok (a, b) ↔
        ∃ va vb : Value, w = .array #[va, vb] ∧ fromValue? va = .ok a ∧ fromValue? vb = .ok b := by
  refine ⟨rfl, fun w => ⟨fun h => ?_, ?_⟩⟩
  · cases w with
    | array items =>
      rcases items with ⟨l⟩
      match l, h with
      | [x, y], h =>
        refine ⟨x, y, rfl, ?_⟩
        rw [fromValue_pair] at h
        cases hx : (fromValue? x : Except String α) with
        | error e =>
          rw [hx] at h
          cases h
        | ok a' =>
          cases hy : (fromValue? y : Except String β) with
          | error e =>
            rw [hx, hy] at h
            cases h
          | ok b' =>
            rw [hx, hy] at h
            cases h
            exact ⟨rfl, rfl⟩
      | [], h => cases h
      | [_], h => cases h
      | _ :: _ :: _ :: _, h => cases h
    | _ => cases h
  · rintro ⟨va, vb, rfl, ha, hb⟩
    rw [fromValue_pair, ha, hb]
    rfl

theorem codec_option {α : Type u} [ToValue α] [FromValue α] [NotNull α] (o : Option α) :
    toValue o = (match o with | none => .null | some a => toValue a) ∧
      ∀ w : Value, fromValue? w = .ok o ↔
        (match o with | none => w = .null | some a => w ≠ .null ∧ fromValue? w = .ok a) := by
  refine ⟨by cases o <;> rfl, fun w => ?_⟩
  by_cases hw : w = .null
  · subst hw
    cases o with
    | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | some a =>
      constructor
      · intro h
        cases h
      · rintro ⟨h, -⟩
        exact (h rfl).elim
  · have key : (fromValue? w : Except String (Option α)) = some <$> (fromValue? w : Except String α) := by
      cases w with
      | null => exact (hw rfl).elim
      | _ => rfl
    rw [key]
    cases o with
    | none =>
      constructor
      · intro h
        cases hx : (fromValue? w : Except String α) with
        | error e =>
          rw [hx] at h
          cases h
        | ok a =>
          rw [hx] at h
          cases h
      · intro h
        exact (hw h).elim
    | some a =>
      constructor
      · intro h
        cases hx : (fromValue? w : Except String α) with
        | error e =>
          rw [hx] at h
          cases h
        | ok a' =>
          rw [hx] at h
          cases h
          exact ⟨hw, rfl⟩
      · rintro ⟨-, h⟩
        rw [h]
        rfl

private theorem mapM_cons_ok {γ : Type v} {δ : Type u} (f : γ → Except String δ) (a : γ) (l : List γ) (r : List δ) :
    (a :: l).mapM f = .ok r ↔ ∃ b bs, f a = .ok b ∧ l.mapM f = .ok bs ∧ r = b :: bs := by
  rw [List.mapM_cons]
  cases f a with
  | error e => simp [bind, Except.bind]
  | ok b =>
    cases l.mapM f with
    | error e => simp [bind, Except.bind]
    | ok bs => simp [bind, Except.bind, pure, Except.pure, eq_comm]

private theorem mapM_ok_congr {γ : Type v} {δ : Type u} {f g : γ → Except String δ} (h : ∀ a b, f a = .ok b ↔ g a = .ok b) :
    ∀ (l : List γ) (r : List δ), l.mapM f = .ok r ↔ l.mapM g = .ok r
  | [], _ => Iff.rfl
  | a :: l, r => by
    rw [mapM_cons_ok, mapM_cons_ok]
    simp only [h a, mapM_ok_congr h l]

private theorem members_eq_ok {α : Type u} [FromValue α] (ms : List (String × Value)) (l : List (String × α)) :
    ms.mapM (fun (k, v) => (k, ·) <$> withContext k (fromValue? v)) = .ok l ↔
      ms.mapM (fun (k, v) => (k, ·) <$> fromValue? v) = .ok l := by
  refine mapM_ok_congr (by
    rintro ⟨k, v⟩ r
    cases h : (fromValue? v : Except String α) <;> simp [h, withContext, Except.mapError, Functor.map, Except.map]) ms l

private theorem members_keys {α : Type u} [FromValue α] :
    ∀ (ms : List (String × Value)) (l : List (String × α)),
      ms.mapM (fun (k, v) => (k, ·) <$> fromValue? v) = .ok l → l.map (·.1) = ms.map (·.1)
  | [], l, h => by cases h; rfl
  | (k, v) :: ms, l, h => by
    obtain ⟨b, bs, hb, hbs, rfl⟩ := (mapM_cons_ok _ _ _ _).mp h
    dsimp only at hb
    cases hv : (fromValue? v : Except String α) with
    | error e => rw [hv] at hb; cases hb
    | ok a =>
      rw [hv] at hb
      cases hb
      simp [members_keys ms bs hbs]

private theorem toList_ofList {α : Type u} (l : List (String × α)) (h : (l.map (·.1)).Pairwise (· < ·)) :
    (Std.ExtTreeMap.ofList l compare).toList = l := by
  have hl : l.Pairwise (fun a b => a.1 < b.1) := List.pairwise_map.mp h
  have hd : l.Pairwise (fun a b => ¬ compare a.1 b.1 = .eq) :=
    hl.imp fun {a b} (hab : a.1 < b.1) (heq : compare a.1 b.1 = .eq) =>
      Std.lt_irrefl ((Std.compare_eq_iff_eq.mp heq) ▸ hab)
  have hmem : ∀ p, p ∈ (Std.ExtTreeMap.ofList l compare).toList ↔ p ∈ l := by
    rintro ⟨k, v⟩
    rw [Std.ExtTreeMap.mem_toList_iff_getElem?_eq_some]
    constructor
    · intro hk
      cases hc : (l.map Prod.fst).contains k with
      | false =>
        rw [Std.ExtTreeMap.getElem?_ofList_of_contains_eq_false hc] at hk
        cases hk
      | true =>
        obtain ⟨⟨k', v'⟩, hp, hpk⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
        simp only at hpk
        subst hpk
        rw [Std.ExtTreeMap.getElem?_ofList_of_mem Std.ReflCmp.compare_self hd hp] at hk
        cases hk
        exact hp
    · intro hk
      exact Std.ExtTreeMap.getElem?_ofList_of_mem Std.ReflCmp.compare_self hd hk
  have hsorted : (Std.ExtTreeMap.ofList l compare).toList.Pairwise (fun a b => a.1 < b.1) :=
    Std.ExtTreeMap.ordered_keys_toList.imp fun h => Std.compare_eq_lt.mp h
  have hnd₁ : (Std.ExtTreeMap.ofList l compare).toList.Nodup :=
    hsorted.imp fun {a b} (hab : a.1 < b.1) (heq : a = b) => Std.lt_irrefl (heq ▸ hab)
  have hnd₂ : l.Nodup := hl.imp fun {a b} (hab : a.1 < b.1) (heq : a = b) => Std.lt_irrefl (heq ▸ hab)
  exact List.Perm.eq_of_pairwise (le := fun a b => a.1 < b.1)
    (fun _ _ _ _ hab hba => absurd (Std.lt_trans hab hba) Std.lt_irrefl) hsorted hl
    ((List.perm_ext_iff_of_nodup hnd₁ hnd₂).mpr hmem)

private theorem ofList_toList {α : Type u} (m : Std.ExtTreeMap String α) : Std.ExtTreeMap.ofList m.toList compare = m :=
  Std.ExtTreeMap.toList_inj.mp (toList_ofList m.toList
    (List.pairwise_map.mpr (Std.ExtTreeMap.ordered_keys_toList.imp fun h => Std.compare_eq_lt.mp h)))

theorem codec_extTreeMap {α : Type u} [ToValue α] [FromValue α] (m : Std.ExtTreeMap String α) :
    toValue m = .table (m.toList.map fun (k, a) => (k, toValue a)).toArray ∧
      ∀ w : Value, fromValue? w = .ok m ↔
        ∃ ms : Array (String × Value), w = .table ms ∧ ms.toList.mapM (fun (k, v) => (k, ·) <$> fromValue? v) = .ok m.toList := by
  refine ⟨rfl, fun w => ?_⟩
  cases w with
  | table ms =>
    simp only [fromValue?]
    constructor
    · intro h
      split at h
      · rename_i hinc
        cases hl : ms.toList.mapM (fun (k, v) => (k, ·) <$> withContext k (fromValue? v : Except String α)) with
        | error e => rw [hl] at h; cases h
        | ok l =>
          rw [hl] at h
          have hm : Std.ExtTreeMap.ofList l compare = m := Except.ok.inj h
          subst hm
          have hl' := (members_eq_ok _ _).mp hl
          refine ⟨ms, rfl, ?_⟩
          rw [toList_ofList l (by rw [members_keys _ _ hl']; exact (keysIncrease_iff _).mp hinc)]
          exact hl'
      · cases h
    · rintro ⟨ms', hms, h⟩
      cases hms
      have hinc : keysIncrease (ms.toList.map (·.1)) = true := by
        rw [keysIncrease_iff, ← members_keys _ _ h]
        exact List.pairwise_map.mpr (Std.ExtTreeMap.ordered_keys_toList.imp fun h => Std.compare_eq_lt.mp h)
      rw [ite_eq_left hinc, (members_eq_ok _ _).mpr h]
      exact congrArg Except.ok (ofList_toList m)
  | _ =>
    simp only [fromValue?, typeMismatch]
    constructor
    · intro h; cases h
    · rintro ⟨_, h, -⟩; cases h

theorem codec_string_rejects_null :
    ¬ ∀ (s : String), @toValue String ⟨fun _ => .null⟩ s = (.string s : Value) ∧
      ∀ w : Value, @fromValue? String ⟨fun _ => .error ""⟩ w = .ok s ↔ w = (.string s : Value) := by
  intro h
  cases (h "").1

theorem codec_decimal_rejects_null :
    ¬ ∀ (d : Decimal), @toValue Decimal ⟨fun _ => .null⟩ d = (.decimal d : Value) ∧
      ∀ w : Value, @fromValue? Decimal ⟨fun _ => .error ""⟩ w = .ok d ↔ w = (.decimal d : Value) := by
  intro h
  cases (h default).1

theorem codec_bool_rejects_null :
    ¬ ∀ (b : Bool), @toValue Bool ⟨fun _ => .null⟩ b = (.boolean b : Value) ∧
      ∀ w : Value, @fromValue? Bool ⟨fun _ => .error ""⟩ w = .ok b ↔ w = (.boolean b : Value) := by
  intro h
  cases (h true).1

theorem codec_int_rejects_null :
    ¬ ∀ (n : Int), @toValue Int ⟨fun _ => .null⟩ n = (.integer n : Value) ∧
      ∀ w : Value, @fromValue? Int ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n : Value) := by
  intro h
  cases (h 0).1

theorem codec_nat_rejects_null :
    ¬ ∀ (n : Nat), @toValue Nat ⟨fun _ => .null⟩ n = (.integer n : Value) ∧
      ∀ w : Value, @fromValue? Nat ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n : Value) := by
  intro h
  cases (h 0).1

theorem codec_uInt8_rejects_null :
    ¬ ∀ (n : UInt8), @toValue UInt8 ⟨fun _ => .null⟩ n = (.integer n.toNat : Value) ∧
      ∀ w : Value, @fromValue? UInt8 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toNat : Value) := by
  intro h
  cases (h 0).1

theorem codec_uInt16_rejects_null :
    ¬ ∀ (n : UInt16), @toValue UInt16 ⟨fun _ => .null⟩ n = (.integer n.toNat : Value) ∧
      ∀ w : Value, @fromValue? UInt16 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toNat : Value) := by
  intro h
  cases (h 0).1

theorem codec_uInt32_rejects_null :
    ¬ ∀ (n : UInt32), @toValue UInt32 ⟨fun _ => .null⟩ n = (.integer n.toNat : Value) ∧
      ∀ w : Value, @fromValue? UInt32 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toNat : Value) := by
  intro h
  cases (h 0).1

theorem codec_uInt64_rejects_null :
    ¬ ∀ (n : UInt64), @toValue UInt64 ⟨fun _ => .null⟩ n = (.integer n.toNat : Value) ∧
      ∀ w : Value, @fromValue? UInt64 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toNat : Value) := by
  intro h
  cases (h 0).1

theorem codec_int8_rejects_null :
    ¬ ∀ (n : Int8), @toValue Int8 ⟨fun _ => .null⟩ n = (.integer n.toInt : Value) ∧
      ∀ w : Value, @fromValue? Int8 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toInt : Value) := by
  intro h
  cases (h 0).1

theorem codec_int16_rejects_null :
    ¬ ∀ (n : Int16), @toValue Int16 ⟨fun _ => .null⟩ n = (.integer n.toInt : Value) ∧
      ∀ w : Value, @fromValue? Int16 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toInt : Value) := by
  intro h
  cases (h 0).1

theorem codec_int32_rejects_null :
    ¬ ∀ (n : Int32), @toValue Int32 ⟨fun _ => .null⟩ n = (.integer n.toInt : Value) ∧
      ∀ w : Value, @fromValue? Int32 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toInt : Value) := by
  intro h
  cases (h 0).1

theorem codec_int64_rejects_null :
    ¬ ∀ (n : Int64), @toValue Int64 ⟨fun _ => .null⟩ n = (.integer n.toInt : Value) ∧
      ∀ w : Value, @fromValue? Int64 ⟨fun _ => .error ""⟩ w = .ok n ↔ w = (.integer n.toInt : Value) := by
  intro h
  cases (h 0).1

theorem codec_char_rejects_null :
    ¬ ∀ (c : Char), @toValue Char ⟨fun _ => .null⟩ c = (.string (String.singleton c) : Value) ∧
      ∀ w : Value, @fromValue? Char ⟨fun _ => .error ""⟩ w = .ok c ↔ w = (.string (String.singleton c) : Value) := by
  intro h
  cases (h 'a').1

theorem codec_array_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (xs : Array α),
      @toValue (Array α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Array β))) (β := α)) xs =
          .array (xs.map toValue) ∧
        ∀ w : Value, @fromValue? (Array α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (Array β))) (β := α)) w = .ok xs ↔
          ∃ vs : Array Value, w = .array vs ∧ vs.toList.mapM fromValue? = .ok xs.toList := by
  intro h
  cases (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ #[]).1

theorem codec_list_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (xs : List α),
      @toValue (List α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (List β))) (β := α)) xs =
          .array (xs.map toValue).toArray ∧
        ∀ w : Value, @fromValue? (List α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (List β))) (β := α)) w = .ok xs ↔
          ∃ vs : Array Value, w = .array vs ∧ vs.toList.mapM fromValue? = .ok xs := by
  intro h
  cases (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ []).1

theorem codec_prod_rejects_null :
    ¬ ∀ {α β : Type u} [ToValue α] [ToValue β] [FromValue α] [FromValue β] (a : α) (b : β),
      @toValue (α × β) ((fun {γ δ : Type u} [ToValue γ] [ToValue δ] => (⟨fun _ => .null⟩ : ToValue (γ × δ))) (γ := α) (δ := β)) (a, b) =
          .array #[toValue a, toValue b] ∧
        ∀ w : Value, @fromValue? (α × β) ((fun {γ δ : Type u} [FromValue γ] [FromValue δ] => (⟨fun _ => .error ""⟩ : FromValue (γ × δ))) (γ := α) (δ := β)) w = .ok (a, b) ↔
          ∃ va vb : Value, w = .array #[va, vb] ∧ fromValue? va = .ok a ∧ fromValue? vb = .ok b := by
  intro h
  cases (@h PUnit PUnit ⟨fun _ => .null⟩ ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ ⟨fun _ => .ok ⟨⟩⟩ ⟨⟩ ⟨⟩).1

theorem codec_option_rejects_constant :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] [NotNull α] (o : Option α),
      @toValue (Option α) ((fun {β : Type u} [ToValue β] [NotNull β] => (⟨fun _ => .null⟩ : ToValue (Option β))) (β := α)) o =
          (match o with | none => .null | some a => toValue a) ∧
        ∀ w : Value, @fromValue? (Option α) ((fun {β : Type u} [ToValue β] [FromValue β] [NotNull β] => (⟨fun _ => .ok none⟩ : FromValue (Option β))) (β := α)) w = .ok o ↔
          (match o with | none => w = .null | some a => w ≠ .null ∧ fromValue? w = .ok a) := by
  intro h
  have := ((@h PUnit ⟨fun _ => .boolean true⟩ ⟨fun _ => .ok ⟨⟩⟩ (@NotNull.mk PUnit ⟨fun _ => .boolean true⟩ fun _ h => nomatch h) none).2 (.integer 0)).mp rfl
  cases this

theorem codec_extTreeMap_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (m : Std.ExtTreeMap String α compare),
      @toValue (Std.ExtTreeMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.ExtTreeMap String β))) (β := α)) m =
          .table (m.toList.map fun (k, a) => (k, toValue a)).toArray ∧
        ∀ w : Value, @fromValue? (Std.ExtTreeMap String α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (Std.ExtTreeMap String β))) (β := α)) w = .ok m ↔
          ∃ ms : Array (String × Value), w = .table ms ∧ ms.toList.mapM (fun (k, v) => (k, ·) <$> fromValue? v) = .ok m.toList := by
  intro h
  cases (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ ∅).1

end ExactJSON
