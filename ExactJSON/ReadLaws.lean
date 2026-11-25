module

public import ExactJSON.Nesting
public import ExactJSON.Fixed
public import ExactJSON.Write

public section

namespace ExactJSON

theorem fromUTF8?_eq_some {b : ByteArray} {s : String} : String.fromUTF8? b = some s ↔ b = s.toByteArray := by
  unfold String.fromUTF8?
  constructor
  · intro h
    split at h
    · cases h
      rfl
    · cases h
  · rintro rfl
    rw [dite_eq_left s.isValidUTF8]
    rfl

theorem readJson_toOption (s : String) : (Value.readJson s).toOption = Rfc8259.read? s := by
  unfold Value.readJson Rfc8259.read?
  split <;> simp_all [Except.toOption]

theorem readJson_ok {s : String} {v : Value} : Value.readJson s = .ok v ↔ Rfc8259.read? s = some v := by
  rw [← readJson_toOption]
  cases Value.readJson s <;> simp [Except.toOption]

theorem read_spelling (sp : Spelling) (maxDepth : Nat) (b : ByteArray) (v : Value) :
    Value.read sp maxDepth b = .ok v ↔ sp.Spells b v ∧ v.depth ≤ maxDepth := by
  unfold Value.read
  cases sp with
  | canonical =>
    constructor
    · intro h
      split at h
      · cases h
      · rename_i s hs
        split at h
        · rename_i hd
          obtain ⟨hread, hr⟩ := (parse_fixed s v).mp h
          refine ⟨⟨Rfc8259.read?_valid _ _ hread, ?_⟩, by rw [← nesting_read hread]; exact hd⟩
          rw [fromUTF8?_eq_some.mp hs, ← hr, Value.render_eq_write]
          rfl
        · cases h
    · rintro ⟨⟨hvalid, hb⟩, hd⟩
      have hs : String.fromUTF8? b = some v.render := by
        rw [fromUTF8?_eq_some, hb, Value.render_eq_write]
        rfl
      have hread := spec_read_render v hvalid
      simp only [hs]
      rw [ite_eq_left (by rw [nesting_read hread]; exact hd)]
      exact render_parse v hvalid
  | any =>
    constructor
    · intro h
      split at h
      · cases h
      · rename_i s hs
        split at h
        · rename_i hd
          have hread := readJson_ok.mp h
          exact ⟨⟨s, hs, hread⟩, by rw [← nesting_read hread]; exact hd⟩
        · cases h
    · rintro ⟨⟨s, hs, hread⟩, hd⟩
      simp only [hs]
      rw [ite_eq_left (by rw [nesting_read hread]; exact hd)]
      exact readJson_ok.mpr hread

theorem foldlM_loop {β : Type} (f : β → UInt8 → β) (as : ByteArray) (h : as.size ≤ as.size) :
    ∀ (i j : Nat) (acc : β), j + i = as.size →
      ByteArray.foldlM.loop (m := Id) (fun b x => pure (f b x)) as as.size h i j acc =
        (as.data.toList.drop j).foldl f acc := by
  have hsize : as.size = as.data.toList.length := (Array.length_toList (xs := as.data)).symm
  intro i
  induction i with
  | zero =>
    intro j acc hj
    unfold ByteArray.foldlM.loop
    rw [dite_eq_right (by omega)]
    rw [List.drop_eq_nil_of_le (by omega)]
    rfl
  | succ i ih =>
    intro j acc hj
    unfold ByteArray.foldlM.loop
    have hlt : j < as.size := by omega
    rw [dite_eq_left hlt]
    show ByteArray.foldlM.loop (m := Id) (fun b x => pure (f b x)) as as.size h i (j + 1) (f acc as[j]) = _
    rw [ih (j + 1) _ (by omega), List.drop_eq_getElem_cons (l := as.data.toList) (i := j) (by omega), List.foldl_cons]
    rfl

theorem byteArray_foldl {β : Type} (f : β → UInt8 → β) (init : β) (b : ByteArray) :
    b.foldl f init = b.data.toList.foldl f init := by
  unfold ByteArray.foldl ByteArray.foldlM
  rw [dite_eq_left (Nat.le_refl _)]
  exact foldlM_loop f b _ b.size 0 init (by omega)

theorem foldl_step (sp : Spelling) (d : Nat) :
    ∀ (l : List UInt8) (arr : Array UInt8), l.foldl Reader.step (⟨sp, d, ⟨arr⟩⟩ : Reader) = ⟨sp, d, ⟨arr ++ l.toArray⟩⟩
  | [], arr => by simp
  | x :: l, arr => by
    rw [List.foldl_cons]
    show l.foldl Reader.step ⟨sp, d, ⟨arr.push x⟩⟩ = _
    rw [foldl_step sp d l (arr.push x)]
    simp

theorem read_streams (sp : Spelling) (maxDepth : Nat) (b : ByteArray) :
    Value.read sp maxDepth b = (b.foldl Reader.step (Reader.start sp maxDepth)).finish := by
  rw [byteArray_foldl]
  show _ = Reader.finish (b.data.toList.foldl Reader.step ⟨sp, maxDepth, ⟨#[]⟩⟩)
  rw [foldl_step]
  simp only [Array.toArray_toList, Array.empty_append]
  rfl

def framed (lines : List ByteArray) : List UInt8 := (lines.map fun l => l.data.toList ++ [10]).flatten

theorem framed_cons (x : ByteArray) (lines : List ByteArray) :
    framed (x :: lines) = x.data.toList ++ 10 :: framed lines := by
  simp [framed]

theorem byteArray_ext {x y : ByteArray} (h : x.data.toList = y.data.toList) : x = y := by
  cases x
  cases y
  simp_all

theorem lineStep_ten (L : Array ByteArray) (cur : ByteArray) : lineStep (L, cur) 10 = (L.push cur, .empty) := rfl

theorem lineStep_other (L : Array ByteArray) (cur : ByteArray) {x : UInt8} (hx : ¬ x = 10) :
    lineStep (L, cur) x = (L, cur.push x) := by
  simp [lineStep, hx]

theorem lineStep_fold : ∀ (l : List UInt8) (L : Array ByteArray) (cur : ByteArray), 10 ∉ cur.data.toList →
    ∃ new : List ByteArray, (l.foldl lineStep (L, cur)).1 = L ++ new.toArray ∧
      cur.data.toList ++ l = framed new ++ (l.foldl lineStep (L, cur)).2.data.toList ∧
      (∀ x ∈ new, 10 ∉ x.data.toList) ∧ 10 ∉ (l.foldl lineStep (L, cur)).2.data.toList
  | [], L, cur, hcur => ⟨[], by simp, by simp [framed], by simp, hcur⟩
  | x :: l, L, cur, hcur => by
    rw [List.foldl_cons]
    by_cases hx : x = 10
    · subst hx
      rw [lineStep_ten]
      obtain ⟨new, h1, h2, h3, h4⟩ := lineStep_fold l (L.push cur) ByteArray.empty (by simp)
      refine ⟨cur :: new, by rw [h1]; simp, ?_, ?_, h4⟩
      · rw [framed_cons, List.append_assoc, List.cons_append, ← h2]
        simp
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hcur
        · exact h3 y hy
    · rw [lineStep_other L cur hx]
      obtain ⟨new, h1, h2, h3, h4⟩ := lineStep_fold l L (cur.push x) (by
        cases cur
        simp only [ByteArray.push, Array.toList_push, List.mem_append, List.mem_singleton, not_or]
        exact ⟨hcur, fun h => hx h.symm⟩)
      refine ⟨new, h1, ?_, h3, h4⟩
      rw [← h2]
      cases cur
      simp [ByteArray.push]

theorem first_line : ∀ (a b r s : List UInt8), 10 ∉ a → 10 ∉ b → a ++ 10 :: r = b ++ 10 :: s → a = b ∧ r = s
  | [], [], r, s, _, _, h => by simpa using h
  | [], y :: b, r, s, _, hb, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hb
  | x :: a, [], r, s, ha, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) ha
  | x :: a, y :: b, r, s, ha, hb, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := first_line a b r s (fun h' => ha (List.mem_cons_of_mem _ h'))
      (fun h' => hb (List.mem_cons_of_mem _ h')) h
    exact ⟨rfl, rfl⟩

theorem framed_unique : ∀ (L1 L2 : List ByteArray) (c1 c2 : List UInt8),
    (∀ x ∈ L1, 10 ∉ x.data.toList) → (∀ x ∈ L2, 10 ∉ x.data.toList) → 10 ∉ c1 → 10 ∉ c2 →
    framed L1 ++ c1 = framed L2 ++ c2 → L1 = L2 ∧ c1 = c2
  | [], [], c1, c2, _, _, _, _, h => ⟨rfl, by simpa [framed] using h⟩
  | [], y :: L2, c1, c2, _, h2, hc1, _, h => by
    rw [framed_cons] at h
    simp only [framed, List.map_nil, List.flatten_nil, List.nil_append] at h
    exact (hc1 (by rw [h]; simp)).elim
  | x :: L1, [], c1, c2, _, _, _, hc2, h => by
    rw [framed_cons] at h
    simp only [framed, List.map_nil, List.flatten_nil, List.nil_append] at h
    exact (hc2 (by rw [← h]; simp)).elim
  | x :: L1, y :: L2, c1, c2, h1, h2, hc1, hc2, h => by
    rw [framed_cons, framed_cons, List.append_assoc, List.append_assoc, List.cons_append, List.cons_append] at h
    obtain ⟨hxy, hrest⟩ := first_line _ _ _ _ (h1 x List.mem_cons_self) (h2 y List.mem_cons_self) h
    obtain ⟨rfl, rfl⟩ := framed_unique L1 L2 c1 c2 (fun z hz => h1 z (List.mem_cons_of_mem _ hz))
      (fun z hz => h2 z (List.mem_cons_of_mem _ hz)) hc1 hc2 hrest
    exact ⟨by rw [byteArray_ext hxy], rfl⟩

theorem size_eq_zero {b : ByteArray} : b.size = 0 ↔ b.data.toList = [] := by
  have : b.size = b.data.toList.length := (Array.length_toList (xs := b.data)).symm
  rw [this, List.length_eq_zero_iff]

theorem splitLines_eq (b : ByteArray) (L : Array ByteArray) :
    splitLines b = some L ↔
      ∃ lines : List ByteArray, L = lines.toArray ∧ b.data.toList = framed lines ∧ ∀ x ∈ lines, 10 ∉ x.data.toList := by
  unfold splitLines
  rw [byteArray_foldl]
  obtain ⟨new, h1, h2, h3, h4⟩ := lineStep_fold b.data.toList #[] ByteArray.empty (by simp)
  generalize b.data.toList.foldl lineStep (#[], ByteArray.empty) = st at h1 h2 h4
  obtain ⟨L', cur⟩ := st
  simp only at h1 h2 h4 ⊢
  simp only [ByteArray.data_empty, Array.toList_empty, List.nil_append] at h2
  rw [h1]
  constructor
  · intro h
    split at h
    · rename_i hcur
      cases h
      refine ⟨new, by simp, ?_, h3⟩
      rw [h2, size_eq_zero.mp hcur, List.append_nil]
    · cases h
  · rintro ⟨lines, rfl, hb, hlines⟩
    obtain ⟨rfl, hc⟩ := framed_unique new lines cur.data.toList [] h3 hlines h4 (by simp) (by rw [← h2, hb]; simp)
    rw [ite_eq_left (size_eq_zero.mpr hc)]
    simp

theorem readNumbered_ok {α : Type} (read : ByteArray → Except String α) :
    ∀ (n : Nat) (ls : List ByteArray) (vs : List α), readNumbered read n ls = .ok vs ↔ ls.mapM read = .ok vs
  | _, [], vs => by simp only [readNumbered, List.mapM_nil]; exact Iff.rfl
  | n, l :: ls, vs => by
    simp only [readNumbered, List.mapM_cons]
    cases hl : read l with
    | error e => simp [bind, Except.bind]
    | ok v =>
      simp only [bind, Except.bind, pure, Except.pure, Functor.map, Except.map]
      have ih := readNumbered_ok read (n + 1) ls
      cases h : readNumbered read (n + 1) ls with
      | error e =>
        cases hm : ls.mapM read with
        | error e' => simp
        | ok ws => exact absurd ((ih ws).mpr hm) (by rw [h]; simp)
      | ok ws => rw [(ih ws).mp h]

theorem readLines_framing (sp : Spelling) (maxDepth : Nat) (b : ByteArray) (vs : Array Value) :
    Value.readLines sp maxDepth b = .ok vs ↔
      ∃ lines : List ByteArray, b.data.toList = (lines.map fun l => l.data.toList ++ [10]).flatten ∧
        (∀ l ∈ lines, 10 ∉ l.data.toList) ∧ lines.mapM (Value.read sp maxDepth) = .ok vs.toList := by
  unfold Value.readLines
  constructor
  · intro h
    split at h
    · cases h
    · rename_i L hL
      obtain ⟨lines, rfl, hb, hlines⟩ := (splitLines_eq b L).mp hL
      refine ⟨lines, hb, hlines, ?_⟩
      cases hr : readNumbered (Value.read sp maxDepth) 1 lines with
      | error e => rw [hr] at h; cases h
      | ok ws =>
        rw [hr] at h
        cases h
        rw [← readNumbered_ok _ 1, hr]
  · rintro ⟨lines, hb, hlines, hmap⟩
    rw [(splitLines_eq b lines.toArray).mpr ⟨lines, rfl, hb, hlines⟩]
    simp only
    rw [(readNumbered_ok _ 1 lines vs.toList).mpr hmap]
    simp [Functor.map, Except.map]

theorem read_spelling_rejects_null :
    ¬ ∀ (sp : Spelling) (maxDepth : Nat) (b : ByteArray) (v : Value),
      (fun (_ : Spelling) (_ : Nat) (_ : ByteArray) => (Except.ok Value.null : Except String Value)) sp maxDepth b =
          .ok v ↔ sp.Spells b v ∧ v.depth ≤ maxDepth := by
  intro h
  have h1 := ((h .canonical 0 "x".toUTF8 .null).mp rfl).1.2
  have h2 : ("x" : String) = "null" := String.toByteArray_inj.mp h1
  exact absurd h2 (by decide)

theorem read_streams_rejects_constant :
    ¬ ∀ (sp : Spelling) (maxDepth : Nat) (b : ByteArray),
      (fun (_ : Spelling) (_ : Nat) (_ : ByteArray) => (Except.error "" : Except String Value)) sp maxDepth b =
        (fun (_ : Unit) => (Except.ok Value.null : Except String Value))
          (b.foldl (fun (r : Unit) (_ : UInt8) => r) ((fun (_ : Spelling) (_ : Nat) => ()) sp maxDepth)) := by
  intro h
  exact nomatch h .canonical 0 ByteArray.empty

theorem readLines_framing_rejects_empty :
    ¬ ∀ (sp : Spelling) (maxDepth : Nat) (b : ByteArray) (vs : Array Value),
      (fun (_ : Spelling) (_ : Nat) (_ : ByteArray) => (Except.ok #[] : Except String (Array Value))) sp maxDepth b =
          .ok vs ↔
        ∃ lines : List ByteArray, b.data.toList = (lines.map fun l => l.data.toList ++ [10]).flatten ∧
          (∀ l ∈ lines, 10 ∉ l.data.toList) ∧ lines.mapM (Value.read sp maxDepth) = .ok vs.toList := by
  intro h
  obtain ⟨lines, hb, -, -⟩ := (h .canonical 0 ⟨#[1]⟩ #[]).mp rfl
  cases lines with
  | nil => simp at hb
  | cons l ls =>
    have : (10 : UInt8) ∈ ([1] : List UInt8) := by
      rw [show ([1] : List UInt8) = (⟨#[1]⟩ : ByteArray).data.toList from rfl, hb]
      simp
    simp at this

end ExactJSON
