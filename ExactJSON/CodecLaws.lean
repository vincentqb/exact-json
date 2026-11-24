module

public import ExactJSON.Codec
public import ExactJSON.FloatBits
import all Init.Data.Array.QSort.Basic

public section

namespace ExactJSON

universe u

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

private theorem foldlM_map_eq_ok {M γ : Type u} {δ : Type} (step : M → δ → Except String M) (f : γ → δ) (g : M → γ → M)
    (hstep : ∀ acc c, step acc (f c) = .ok (g acc c)) :
    ∀ (l : List γ) (init : M), List.foldlM step init (l.map f) = .ok (l.foldl g init)
  | [], _ => rfl
  | c :: l, init => by
    rw [List.map_cons, List.foldlM_cons, hstep]
    exact foldlM_map_eq_ok step f g hstep l (g init c)

private theorem treeMap_ofList_toList {α : Type u} (m : Std.TreeMap String α) :
    (Std.TreeMap.ofList m.toList compare).Equiv m := by
  apply Std.TreeMap.Equiv.of_forall_constGet?_eq
  intro k
  cases h : m[k]? with
  | some v =>
    exact Std.TreeMap.getElem?_ofList_of_mem Std.ReflCmp.compare_self Std.TreeMap.distinct_keys_toList
      (Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr h)
  | none =>
    apply Std.TreeMap.getElem?_ofList_of_contains_eq_false
    cases hc : (m.toList.map Prod.fst).contains k with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨p, hp, hpk⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
      subst hpk
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hp] at h
      cases h

private def Rearranges {α : Type u} {n : Nat} (lo hi : Nat) (v v' : Vector α n) : Prop :=
  (∀ j (hj : j < n), (j < lo ∨ hi < j) → v'[j] = v[j]) ∧
    ∀ j (hj : j < n), lo ≤ j → j ≤ hi → ∃ (j' : Nat) (hj' : j' < n), lo ≤ j' ∧ j' ≤ hi ∧ v'[j] = v[j']

private theorem rearranges_refl {α : Type u} {n : Nat} (lo hi : Nat) (v : Vector α n) : Rearranges lo hi v v :=
  ⟨fun _ _ _ => rfl, fun j hj h1 h2 => ⟨j, hj, h1, h2, rfl⟩⟩

private theorem rearranges_trans {α : Type u} {n : Nat} {lo hi : Nat} {v v' v'' : Vector α n}
    (h : Rearranges lo hi v v') (h' : Rearranges lo hi v' v'') : Rearranges lo hi v v'' := by
  refine ⟨fun j hj hout => (h'.1 j hj hout).trans (h.1 j hj hout), fun j hj h1 h2 => ?_⟩
  obtain ⟨j', hj', h1', h2', e'⟩ := h'.2 j hj h1 h2
  obtain ⟨j'', hj'', h1'', h2'', e''⟩ := h.2 j' hj' h1' h2'
  exact ⟨j'', hj'', h1'', h2'', e'.trans e''⟩

private theorem rearranges_mono {α : Type u} {n : Nat} {lo hi lo' hi' : Nat} {v v' : Vector α n}
    (h : Rearranges lo' hi' v v') (hlo : lo ≤ lo') (hhi : hi' ≤ hi) : Rearranges lo hi v v' := by
  refine ⟨fun j hj hout => h.1 j hj (by omega), fun j hj h1 h2 => ?_⟩
  by_cases hin : lo' ≤ j ∧ j ≤ hi'
  · obtain ⟨j', hj', h1', h2', e⟩ := h.2 j hj hin.1 hin.2
    exact ⟨j', hj', by omega, by omega, e⟩
  · exact ⟨j, hj, h1, h2, h.1 j hj (by omega)⟩

private theorem rearranges_swap {α : Type u} {n : Nat} {lo hi : Nat} (v : Vector α n) (i k : Nat)
    (hi' : i < n) (hk : k < n) (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : lo ≤ k) (h4 : k ≤ hi) :
    Rearranges lo hi v (v.swap i k hi' hk) := by
  refine ⟨fun j hj hout => ?_, fun j hj h5 h6 => ?_⟩
  · rw [Vector.getElem_swap]
    split
    · omega
    · split
      · omega
      · rfl
  · rw [Vector.getElem_swap]
    split
    · exact ⟨k, hk, h3, h4, rfl⟩
    · split
      · exact ⟨i, hi', h1, h2, rfl⟩
      · exact ⟨j, hj, h5, h6, rfl⟩

private theorem rearranges_ite_swap {α : Type u} {n : Nat} {lo hi : Nat} (c : Bool) (v : Vector α n) (i k : Nat)
    (hi' : i < n) (hk : k < n) (h1 : lo ≤ i) (h2 : i ≤ hi) (h3 : lo ≤ k) (h4 : k ≤ hi) :
    Rearranges lo hi v (if c = true then v.swap i k hi' hk else v) := by
  split
  · exact rearranges_swap v i k hi' hk h1 h2 h3 h4
  · exact rearranges_refl lo hi v

private theorem perm_ite_swap {α : Type u} {n : Nat} (c : Bool) (v : Vector α n) (i k : Nat)
    (hi' : i < n) (hk : k < n) : (if c = true then v.swap i k hi' hk else v).Perm v := by
  split
  · exact Vector.swap_perm hi' hk
  · exact Vector.Perm.refl v

private theorem ite_swap_ordered {α : Type u} (lt : α → α → Bool)
    (asymm : ∀ a b, lt a b = true → lt b a = false) {n : Nat} (v : Vector α n) (i k : Nat)
    (hi' : i < n) (hk : k < n) :
    lt (if lt v[i] v[k] = true then v.swap i k hi' hk else v)[i] (if lt v[i] v[k] = true then v.swap i k hi' hk else v)[k] = false := by
  split
  · rename_i h
    rw [Vector.getElem_swap_left, Vector.getElem_swap_right]
    exact asymm _ _ h
  · rename_i h
    simpa using h

private theorem qpartition_loop_spec {α : Type u} (lt : α → α → Bool) {n : Nat} (lo hi : Nat) (hhi : hi < n) (p : α)
    (v₀ : Vector α n) (hp : v₀[hi] = p) (mid : Nat) (hmid : mid < hi)
    (hmidv : lt (v₀[mid]'(by omega)) p = false) :
    ∀ (d : Nat) (u : Vector α n) (i k : Nat) (ilo : lo ≤ i) (ik : i ≤ k) (w : k ≤ hi), hi - k = d →
      (∀ j (hj : j < n), (j < lo ∨ k ≤ j) → u[j] = v₀[j]) →
      Rearranges lo hi v₀ u → u.Perm v₀ →
      (∀ j (hj : j < n), lo ≤ j → j < i → lt u[j] p = true) →
      (∀ j (hj : j < n), i ≤ j → j < k → lt u[j] p = false) →
      (mid < k → i < k) →
      ∀ (m : Nat) (hm : lo ≤ m ∧ m ≤ hi) (u' : Vector α n),
        Array.qpartition.loop lt lo hi hhi p u i k ilo ik w = (⟨m, hm⟩, u') →
        Rearranges lo hi v₀ u' ∧ u'.Perm v₀ ∧
        (∀ j (hj : j < n), lo ≤ j → j < m → lt u'[j] (u'[m]'(Nat.lt_of_le_of_lt hm.2 hhi)) = true) ∧
        (∀ j (hj : j < n), m < j → j ≤ hi → lt u'[j] (u'[m]'(Nat.lt_of_le_of_lt hm.2 hhi)) = false) ∧
        m < hi := by
  intro d
  induction d with
  | zero =>
    intro u i k ilo ik w hd hout hwin hperm hlow hhigh hmk m hm u' heq
    rw [Array.qpartition.loop.eq_def, dite_eq_right (by omega)] at heq
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    have hik : i < hi := by have := hmk (by omega); omega
    have hpiv : u[hi] = p := by rw [hout hi hhi (Or.inr (by omega)), hp]
    refine ⟨rearranges_trans hwin (rearranges_swap u i hi _ hhi ilo (by omega) (by omega) (Nat.le_refl _)),
      (Vector.swap_perm _ _).trans hperm, fun j hj h1 h2 => ?_, fun j hj h1 h2 => ?_, hik⟩
    · rw [Vector.getElem_swap_left, Vector.getElem_swap_of_ne (by omega) (by omega), hpiv]
      exact hlow j hj h1 h2
    · rw [Vector.getElem_swap_left, hpiv]
      by_cases hj' : j = hi
      · subst hj'
        rw [Vector.getElem_swap_right]
        exact hhigh i (by omega) (Nat.le_refl _) (by omega)
      · rw [Vector.getElem_swap_of_ne (by omega) hj']
        exact hhigh j hj (by omega) (by omega)
  | succ d ih =>
    intro u i k ilo ik w hd hout hwin hperm hlow hhigh hmk m hm u' heq
    have hk : k < hi := by omega
    rw [Array.qpartition.loop.eq_def, dite_eq_left hk] at heq
    split at heq
    · rename_i hlt
      refine ih (u.swap i k (by omega) (by omega)) (i + 1) (k + 1) _ _ _ (by omega) ?_
        (rearranges_trans hwin (rearranges_swap u i k _ _ ilo (by omega) (by omega) (by omega)))
        ((Vector.swap_perm _ _).trans hperm) ?_ ?_ ?_ m hm u' heq
      · intro j hj hj'
        rw [Vector.getElem_swap_of_ne (by omega) (by omega)]
        exact hout j hj (by omega)
      · intro j hj h1 h2
        by_cases hji : j = i
        · subst hji
          rw [Vector.getElem_swap_left]
          exact hlt
        · rw [Vector.getElem_swap_of_ne hji (by omega)]
          exact hlow j hj h1 (by omega)
      · intro j hj h1 h2
        by_cases hjk : j = k
        · subst hjk
          rw [Vector.getElem_swap_right]
          exact hhigh i (by omega) (Nat.le_refl _) (by omega)
        · rw [Vector.getElem_swap_of_ne (by omega) hjk]
          exact hhigh j hj (by omega) (by omega)
      · intro h
        by_cases hmk' : mid = k
        · subst hmk'
          rw [hout mid (by omega) (Or.inr (Nat.le_refl _))] at hlt
          rw [hmidv] at hlt
          cases hlt
        · have := hmk (by omega)
          omega
    · rename_i hlt
      refine ih u i (k + 1) ilo (by omega) (by omega) (by omega) ?_ hwin hperm hlow ?_ (fun _ => by omega) m hm u' heq
      · intro j hj hj'
        exact hout j hj (by omega)
      · intro j hj h1 h2
        by_cases hjk : j = k
        · subst hjk
          simpa using hlt
        · exact hhigh j hj h1 (by omega)

private theorem qpartition_spec {α : Type u} (lt : α → α → Bool)
    (asymm : ∀ a b, lt a b = true → lt b a = false) {n : Nat} (v : Vector α n) (lo hi : Nat)
    (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n) (hlt : lo < hi) :
    ∀ (m : Nat) (hm : lo ≤ m ∧ m ≤ hi) (v' : Vector α n), Array.qpartition v lt lo hi w hlo hhi = (⟨m, hm⟩, v') →
      Rearranges lo hi v v' ∧ v'.Perm v ∧
      (∀ j (hj : j < n), lo ≤ j → j < m → lt v'[j] (v'[m]'(Nat.lt_of_le_of_lt hm.2 hhi)) = true) ∧
      (∀ j (hj : j < n), m < j → j ≤ hi → lt v'[j] (v'[m]'(Nat.lt_of_le_of_lt hm.2 hhi)) = false) ∧
      m < hi := by
  intro m hm v' heq
  unfold Array.qpartition at heq
  dsimp only at heq
  have hmid : (lo + hi) / 2 < hi := by omega
  have hmid' : (lo + hi) / 2 < n := by omega
  obtain ⟨h1, h2, h3, h4, h5⟩ := qpartition_loop_spec lt lo hi hhi _ _ rfl ((lo + hi) / 2) hmid
    (ite_swap_ordered lt asymm _ _ _ hmid' hhi) (hi - lo) _ lo lo (Nat.le_refl _) (Nat.le_refl _) w rfl
    (fun _ _ _ => rfl) (rearranges_refl _ _ _) (Vector.Perm.refl _) (fun j _ h1 h2 => absurd h2 (by omega))
    (fun j _ h1 h2 => absurd h2 (by omega)) (fun h => absurd h (by omega)) m hm v' heq
  refine ⟨rearranges_trans ?_ h1, h2.trans ?_, h3, h4, h5⟩
  · exact rearranges_trans (rearranges_trans (rearranges_ite_swap _ _ _ _ _ _ (Nat.le_refl _) w (by omega) (by omega))
      (rearranges_ite_swap _ _ _ _ _ _ (Nat.le_refl _) w w (Nat.le_refl _)))
      (rearranges_ite_swap _ _ _ _ _ _ (by omega) (by omega) w (Nat.le_refl _))
  · exact (perm_ite_swap _ _ _ _ _ _).trans ((perm_ite_swap _ _ _ _ _ _).trans (perm_ite_swap _ _ _ _ _ _))

private def SortedOn {α : Type u} (lt : α → α → Bool) {n : Nat} (lo hi : Nat) (v : Vector α n) : Prop :=
  ∀ (j₁ j₂ : Nat) (h₁ : j₁ < n) (h₂ : j₂ < n), lo ≤ j₁ → j₁ < j₂ → j₂ ≤ hi → lt v[j₂] v[j₁] = false

private theorem qsort_sort_spec {α : Type u} (lt : α → α → Bool) (irrefl : ∀ a, lt a a = false)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (ntrans : ∀ a b c, lt a c = true → lt a b = true ∨ lt b c = true) {n : Nat} :
    ∀ (B : Nat) (v : Vector α n) (lo hi : Nat) (w : lo ≤ hi) (hlo : lo < n) (hhi : hi < n), hi - lo < B →
      Rearranges lo hi v (Array.qsort.sort lt v lo hi w hlo hhi) ∧ (Array.qsort.sort lt v lo hi w hlo hhi).Perm v ∧
        SortedOn lt lo hi (Array.qsort.sort lt v lo hi w hlo hhi) := by
  have asymm : ∀ a b, lt a b = true → lt b a = false := fun a b h => by
    cases h' : lt b a
    · rfl
    · have := trans a b a h h'
      rw [irrefl] at this
      cases this
  intro B
  induction B with
  | zero =>
    intro v lo hi w hlo hhi hB
    omega
  | succ B ih =>
    intro v lo hi w hlo hhi hB
    rw [Array.qsort.sort.eq_def]
    split
    · rename_i hlt
      split
      rename_i mid hmid v' heq
      obtain ⟨p1, p2, p3, p4, p5⟩ := qpartition_spec lt asymm v lo hi w hlo hhi hlt mid hmid v' heq
      rw [dite_eq_right (by omega)]
      obtain ⟨q1, q2, q3⟩ := ih v' lo mid hmid.1 hlo (by omega) (by omega)
      obtain ⟨r1, r2, r3⟩ := ih (Array.qsort.sort lt v' lo mid hmid.1 hlo (by omega)) (mid + 1) hi (by omega)
        (by omega) hhi (by omega)
      refine ⟨rearranges_trans p1 (rearranges_trans (rearranges_mono q1 (Nat.le_refl _) (by omega))
        (rearranges_mono r1 (by omega) (Nat.le_refl _))), r2.trans (q2.trans p2), fun j₁ j₂ h₁ h₂ hl hj hh => ?_⟩
      by_cases c2 : j₂ ≤ mid
      · rw [r1.1 j₁ h₁ (Or.inl (by omega)), r1.1 j₂ h₂ (Or.inl (by omega))]
        exact q3 j₁ j₂ h₁ h₂ hl hj c2
      · by_cases c1 : mid + 1 ≤ j₁
        · exact r3 j₁ j₂ h₁ h₂ c1 hj hh
        · rw [r1.1 j₁ h₁ (Or.inl (by omega))]
          obtain ⟨j₁', hj₁', a1, a2, e1⟩ := q1.2 j₁ h₁ hl (by omega)
          obtain ⟨j₂', hj₂', b1, b2, e2⟩ := r1.2 j₂ h₂ (by omega) hh
          rw [e1, e2, q1.1 j₂' hj₂' (Or.inr (by omega))]
          have hb := p4 j₂' hj₂' (by omega) b2
          cases hc : lt v'[j₂'] v'[j₁']
          · rfl
          · exfalso
            rcases ntrans _ (v'[mid]'(by omega)) _ hc with hc' | hc'
            · rw [hb] at hc'
              cases hc'
            · by_cases hj1 : j₁' = mid
              · subst hj1
                rw [irrefl] at hc'
                cases hc'
              · have := trans _ _ _ hc' (p3 j₁' hj₁' a1 (by omega))
                rw [irrefl] at this
                cases this
    · rename_i hlt
      exact ⟨rearranges_refl _ _ _, Vector.Perm.refl _, fun j₁ j₂ _ _ h1 h2 h3 => absurd hlt (by omega)⟩

private theorem qsort_spec {α : Type u} (as : Array α) (lt : α → α → Bool) (irrefl : ∀ a, lt a a = false)
    (trans : ∀ a b c, lt a b = true → lt b c = true → lt a c = true)
    (ntrans : ∀ a b c, lt a c = true → lt a b = true ∨ lt b c = true) :
    (as.qsort lt).toList.Perm as.toList ∧ (as.qsort lt).toList.Pairwise (fun a b => lt b a = false) := by
  unfold Array.qsort
  split
  · rename_i h
    refine ⟨List.Perm.refl _, ?_⟩
    rw [List.eq_nil_of_length_eq_zero h]
    exact List.Pairwise.nil
  · rename_i h
    dsimp only
    obtain ⟨-, s2, s3⟩ := qsort_sort_spec lt irrefl trans ntrans (as.size + 1) as.toVector (min 0 (as.size - 1))
      (max (min 0 (as.size - 1)) (min (as.size - 1) (as.size - 1))) (by omega) (by omega) (by omega) (by omega)
    refine ⟨s2.toList, List.pairwise_iff_getElem.mpr fun i j hi hj hij => ?_⟩
    simp only [Array.length_toList, Vector.size_toArray] at hi hj
    simp only [Array.getElem_toList, Vector.getElem_toArray]
    exact s3 i j hi hj (by omega) hij (by omega)

private theorem exists_perm_of_perm_map {γ : Type u} {δ : Type} (f : γ → δ) {l₁ l₂ : List δ} (h : l₁.Perm l₂) :
    ∀ L : List γ, L.map f = l₂ → ∃ L' : List γ, L'.Perm L ∧ L'.map f = l₁ := by
  induction h with
  | nil =>
    intro L hL
    cases L with
    | nil => exact ⟨[], List.Perm.refl _, rfl⟩
    | cons _ _ => cases hL
  | cons x _ ih =>
    intro L hL
    cases L with
    | nil => cases hL
    | cons y L₀ =>
      simp only [List.map_cons, List.cons.injEq] at hL
      obtain ⟨hy, hL₀⟩ := hL
      obtain ⟨L', hp, hm⟩ := ih L₀ hL₀
      exact ⟨y :: L', hp.cons y, by rw [List.map_cons, hm, hy]⟩
  | swap x y l =>
    intro L hL
    match L, hL with
    | a :: b :: L₀, hL =>
      simp only [List.map_cons, List.cons.injEq] at hL
      obtain ⟨ha, hb, hL₀⟩ := hL
      exact ⟨b :: a :: L₀, List.Perm.swap a b L₀, by simp [ha, hb, hL₀]⟩
  | trans _ _ ih₁ ih₂ =>
    intro L hL
    obtain ⟨L₂, hp₂, hm₂⟩ := ih₂ L hL
    obtain ⟨L₁, hp₁, hm₁⟩ := ih₁ L₂ hm₂
    exact ⟨L₁, hp₁.trans hp₂, hm₁⟩

private theorem keysIncreaseFrom_of_pairwise : ∀ (k : String) (l : List String),
    (k :: l).Pairwise (· < ·) → keysIncreaseFrom k l = true
  | _, [], _ => rfl
  | k, k' :: l, h => by
    simp only [keysIncreaseFrom, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨List.rel_of_pairwise_cons h List.mem_cons_self, keysIncreaseFrom_of_pairwise k' l (List.Pairwise.of_cons h)⟩

private theorem keysIncrease_of_pairwise : ∀ l : List String, l.Pairwise (· < ·) → keysIncrease l = true
  | [], _ => rfl
  | k :: l, h => keysIncreaseFrom_of_pairwise k l h

private theorem hashMap_ofList_perm {α : Type u} (m : Std.HashMap String α) (L : List (String × α))
    (h : L.Perm m.toList) : (Std.HashMap.ofList L).Equiv m := by
  have hd : L.Pairwise (fun a b => (a.1 == b.1) = false) :=
    h.symm.pairwise Std.HashMap.distinct_keys_toList (fun hxy => by rw [BEq.comm]; exact hxy)
  apply Std.HashMap.Equiv.of_forall_getElem?_eq
  intro k
  cases hk : m[k]? with
  | some v =>
    exact Std.HashMap.getElem?_ofList_of_mem BEq.rfl hd
      (h.mem_iff.mpr (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hk))
  | none =>
    apply Std.HashMap.getElem?_ofList_of_contains_eq_false
    cases hc : (L.map Prod.fst).contains k with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨p, hp, hpk⟩ := List.mem_map.mp (List.contains_iff_mem.mp hc)
      subst hpk
      rw [Std.HashMap.mem_toList_iff_getElem?_eq_some.mp (h.mem_iff.mp hp)] at hk
      cases hk

theorem codec_value (v : Value) :
    toValue v = (v : Value) ∧ ∀ w : Value, fromValue? w = .ok v ↔ w = (v : Value) := by
  refine ⟨rfl, fun w => ?_⟩
  show (Except.ok w : Except String Value) = .ok v ↔ w = v
  exact ⟨fun h => by cases h; rfl, fun h => by rw [h]⟩

theorem codec_string (s : String) :
    toValue s = (.string s : Value) ∧ ∀ w : Value, fromValue? w = .ok s ↔ w = (.string s : Value) := by
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

theorem codec_float (x : Float) :
    toValue x = (if x.isNaN then .string "NaN" else if x.isInf then .string (if x > 0 then "Infinity" else "-Infinity") else .float x : Value) ∧
      ∀ w : Value, fromValue? w = .ok x ↔
        w = .float x ∨ (w = .string "NaN" ∧ x = Float.nan) ∨ (w = .string "Infinity" ∧ x = Float.inf) ∨
        (w = .string "-Infinity" ∧ x = -Float.inf) := by
  have hnan : (0.0 / 0.0 : Float) = Float.nan := FloatText.toBits_inj (by decide +kernel)
  have hinf : (1.0 / 0.0 : Float) = Float.inf := FloatText.toBits_inj (by decide +kernel)
  have hninf : (-1.0 / 0.0 : Float) = -Float.inf := FloatText.toBits_inj (by decide +kernel)
  refine ⟨rfl, fun w => ?_⟩
  simp only [fromValue?]
  split
  · simp [pure_eq_ok]
  · simp [hnan, pure_eq_ok, eq_comm]
  · simp [hinf, pure_eq_ok, eq_comm]
  · simp [hninf, pure_eq_ok, eq_comm]
  · rename_i h1 h2 h3 h4
    constructor
    · intro h
      cases h
    · rintro (h | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · exact (h1 x h).elim
      · exact (h2 h).elim
      · exact (h3 h).elim
      · exact (h4 h).elim

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

theorem codec_treeMap {α : Type u} [ToValue α] [FromValue α] (m : Std.TreeMap String α) :
    toValue m = .table (m.toArray.map fun (k, a) => (k, toValue a)) ∧
      ((∀ a : α, fromValue? (toValue a) = .ok a) →
        ∃ m' : Std.TreeMap String α, fromValue? (toValue m) = .ok m' ∧ m'.toList = m.toList) := by
  refine ⟨rfl, fun lawful => ⟨m.toList.foldl (fun acc p => acc.insert p.1 p.2) ∅, ?_, ?_⟩⟩
  · simp only [toValue, fromValue?]
    rw [← Array.foldlM_toList, Array.toList_map, Std.TreeMap.toList_toArray]
    refine foldlM_map_eq_ok _ _ _ ?_ m.toList ∅
    rintro acc ⟨k, a⟩
    show (withContext k (fromValue? (toValue a)) >>= fun r => pure (acc.insert k r)) = _
    rw [lawful]
    rfl
  · exact Std.TreeMap.Equiv.toList_eq (Std.TreeMap.ofList_equiv_foldl.symm.trans (treeMap_ofList_toList m))

theorem codec_hashMap {α : Type u} [ToValue α] [FromValue α] (m : Std.HashMap String α) :
    (∃ l : List (String × Value), toValue m = .table ⟨l⟩ ∧ keysIncrease (l.map (·.1)) = true ∧
      l.Perm (m.toList.map fun (k, a) => (k, toValue a))) ∧
      ((∀ a : α, fromValue? (toValue a) = .ok a) →
        ∃ m' : Std.HashMap String α, fromValue? (toValue m) = .ok m' ∧ m'.toList.Perm m.toList) := by
  have irrefl : ∀ a : String × Value, decide (a.1 < a.1) = false := fun a => decide_eq_false Std.lt_irrefl
  have trans : ∀ a b c : String × Value, decide (a.1 < b.1) = true → decide (b.1 < c.1) = true →
      decide (a.1 < c.1) = true := fun a b c h1 h2 => by
    simp only [decide_eq_true_eq] at h1 h2 ⊢
    exact Std.lt_trans h1 h2
  have ntrans : ∀ a b c : String × Value, decide (a.1 < c.1) = true →
      decide (a.1 < b.1) = true ∨ decide (b.1 < c.1) = true := fun a b c h => by
    simp only [decide_eq_true_eq] at h ⊢
    rcases Std.lt_trichotomy a.1 b.1 with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (h' ▸ h)
    · exact Or.inr (Std.lt_trans h' h)
  obtain ⟨hperm, hsorted⟩ := qsort_spec (m.toArray.map (fun (k, a) => (k, toValue a) : String × α → String × Value))
    (fun x y => decide (x.1 < y.1)) irrefl trans ntrans
  rw [Array.toList_map, Std.HashMap.toList_toArray] at hperm
  refine ⟨⟨_, rfl, ?_, hperm⟩, fun lawful => ?_⟩
  · apply keysIncrease_of_pairwise
    rw [List.pairwise_map]
    have hd0 : (m.toList.map (fun (k, a) => (k, toValue a) : String × α → String × Value)).Pairwise
        (fun a b => a.1 ≠ b.1) :=
      List.pairwise_map.mpr (Std.HashMap.distinct_keys_toList.imp fun h => by simpa using h)
    have hd := hperm.symm.pairwise hd0 (fun h => Ne.symm h)
    refine (hsorted.and hd).imp fun {a b} h => ?_
    obtain ⟨h1, h2⟩ := h
    rcases Std.lt_trichotomy a.1 b.1 with h' | h' | h'
    · exact h'
    · exact absurd h' h2
    · simp only [decide_eq_false_iff_not] at h1
      exact absurd h' h1
  · obtain ⟨L', hL'perm, hL'map⟩ :=
      exists_perm_of_perm_map (fun (k, a) => (k, toValue a) : String × α → String × Value) hperm m.toList rfl
    refine ⟨L'.foldl (fun acc p => acc.insert p.1 p.2) ∅, ?_, ?_⟩
    · show Array.foldlM _ {} ((m.toArray.map (fun (k, a) => (k, toValue a) : String × α → String × Value)).qsort
        (fun x y => decide (x.1 < y.1))) = _
      rw [← Array.foldlM_toList, ← hL'map]
      refine foldlM_map_eq_ok _ _ _ ?_ L' ∅
      rintro acc ⟨k, a⟩
      show (withContext k (fromValue? (toValue a)) >>= fun r => pure (acc.insert k r)) = _
      rw [lawful]
      rfl
    · exact Std.HashMap.Equiv.toList_perm
        (Std.HashMap.ofList_equiv_foldl.symm.trans (hashMap_ofList_perm m L' hL'perm))

theorem codec_value_rejects_null :
    ¬ ∀ (v : Value), @toValue Value ⟨fun _ => .null⟩ v = (v : Value) ∧
      ∀ w : Value, @fromValue? Value ⟨fun _ => .error ""⟩ w = .ok v ↔ w = (v : Value) := by
  intro h
  cases (h (.integer 0)).1

theorem codec_string_rejects_null :
    ¬ ∀ (s : String), @toValue String ⟨fun _ => .null⟩ s = (.string s : Value) ∧
      ∀ w : Value, @fromValue? String ⟨fun _ => .error ""⟩ w = .ok s ↔ w = (.string s : Value) := by
  intro h
  cases (h "").1

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

theorem codec_float_rejects_null :
    ¬ ∀ (x : Float), @toValue Float ⟨fun _ => .null⟩ x = (if x.isNaN then .string "NaN" else if x.isInf then .string (if x > 0 then "Infinity" else "-Infinity") else .float x : Value) ∧
      ∀ w : Value, @fromValue? Float ⟨fun _ => .error ""⟩ w = .ok x ↔
        w = .float x ∨ (w = .string "NaN" ∧ x = Float.nan) ∨ (w = .string "Infinity" ∧ x = Float.inf) ∨
        (w = .string "-Infinity" ∧ x = -Float.inf) := by
  intro h
  have := (h 0.0).1
  split at this
  · cases this
  · split at this
    · cases this
    · cases this

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
        ∀ w : Value, @fromValue? (Option α) ((fun {β : Type u} [FromValue β] [NotNull β] => (⟨fun _ => .ok none⟩ : FromValue (Option β))) (β := α)) w = .ok o ↔
          (match o with | none => w = .null | some a => w ≠ .null ∧ fromValue? w = .ok a) := by
  intro h
  have := ((@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ ⟨⟩ none).2 (.integer 0)).mp rfl
  cases this

theorem codec_treeMap_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (m : Std.TreeMap String α),
      @toValue (Std.TreeMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.TreeMap String β))) (β := α)) m =
          .table (m.toArray.map fun (k, a) => (k, toValue a)) ∧
        ((∀ a : α, fromValue? (toValue a) = .ok a) →
          ∃ m' : Std.TreeMap String α,
            @fromValue? (Std.TreeMap String α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (Std.TreeMap String β))) (β := α))
              (@toValue (Std.TreeMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.TreeMap String β))) (β := α)) m) = .ok m' ∧
            m'.toList = m.toList) := by
  intro h
  cases (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ ∅).1

theorem codec_hashMap_rejects_null :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (m : Std.HashMap String α),
      (∃ l : List (String × Value),
        @toValue (Std.HashMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.HashMap String β))) (β := α)) m = .table ⟨l⟩ ∧
          keysIncrease (l.map (·.1)) = true ∧ l.Perm (m.toList.map fun (k, a) => (k, toValue a))) ∧
        ((∀ a : α, fromValue? (toValue a) = .ok a) →
          ∃ m' : Std.HashMap String α,
            @fromValue? (Std.HashMap String α) ((fun {β : Type u} [FromValue β] => (⟨fun _ => .error ""⟩ : FromValue (Std.HashMap String β))) (β := α))
              (@toValue (Std.HashMap String α) ((fun {β : Type u} [ToValue β] => (⟨fun _ => .null⟩ : ToValue (Std.HashMap String β))) (β := α)) m) = .ok m' ∧
            m'.toList.Perm m.toList) := by
  intro h
  obtain ⟨l, hl, -⟩ := (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ ∅).1
  cases hl

end ExactJSON
