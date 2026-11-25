module

public import ExactJSON.Read
public import ExactJSON.NumberText

public section

namespace ExactJSON

open Rfc8259

abbrev Outside (k m : Nat) : Nesting := ⟨false, false, k, m⟩

abbrev Inside (k m : Nat) : Nesting := ⟨true, false, k, m⟩

theorem next_inside {k m : Nat} {c : Char} (h1 : c ≠ '"') (h2 : c ≠ '\\') : (Inside k m).next c = Inside k m := by
  simp [Nesting.next, h1, h2]

theorem next_inside_quote {k m : Nat} : (Inside k m).next '"' = Outside k m := by
  simp [Nesting.next]

theorem next_escape {k m : Nat} (c : Char) : ((Inside k m).next '\\').next c = Inside k m := by
  simp [Nesting.next]

theorem next_outside {k m : Nat} {c : Char} (h1 : c ≠ '"') (h2 : c ≠ '[') (h3 : c ≠ '{') (h4 : c ≠ ']')
    (h5 : c ≠ '}') : (Outside k m).next c = Outside k m := by
  simp [Nesting.next, h1, h2, h3, h4, h5]

theorem next_outside_quote {k m : Nat} : (Outside k m).next '"' = Inside k m := by
  simp [Nesting.next]

theorem next_open {k m : Nat} {c : Char} (h : c = '[' ∨ c = '{') :
    (Outside k m).next c = Outside (k + 1) (max m (k + 1)) := by
  rcases h with rfl | rfl <;> simp [Nesting.next]

theorem next_close {k m : Nat} {c : Char} (h : c = ']' ∨ c = '}') : (Outside (k + 1) m).next c = Outside k m := by
  rcases h with rfl | rfl <;> simp [Nesting.next]

theorem hexValue?_plain {c : Char} {n : Nat} (h : hexValue? c = some n) : c ≠ '"' ∧ c ≠ '\\' := by
  constructor <;> (rintro rfl; simp [hexValue?] at h)

theorem hex4?_plain {a b c d : Char} {u : Nat} (h : hex4? a b c d = some u) :
    (a ≠ '"' ∧ a ≠ '\\') ∧ (b ≠ '"' ∧ b ≠ '\\') ∧ (c ≠ '"' ∧ c ≠ '\\') ∧ (d ≠ '"' ∧ d ≠ '\\') := by
  unfold hex4? at h
  cases ha : hexValue? a <;> cases hb : hexValue? b <;> cases hc : hexValue? c <;> cases hd : hexValue? d <;>
    simp_all [bind, Option.bind] <;>
    exact ⟨hexValue?_plain ha, hexValue?_plain hb, hexValue?_plain hc, hexValue?_plain hd⟩

theorem foldl_inside_hex {k m : Nat} {a b c d : Char} {u : Nat} (h : hex4? a b c d = some u) (rest : List Char) :
    ('\\' :: 'u' :: a :: b :: c :: d :: rest).foldl Nesting.next (Inside k m) = rest.foldl Nesting.next (Inside k m) := by
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩, ⟨d1, d2⟩⟩ := hex4?_plain h
  simp only [List.foldl_cons, next_escape, next_inside a1 a2, next_inside b1 b2, next_inside c1 c2, next_inside d1 d2]

theorem foldl_chars (input acc : List Char) :
    ∀ (cs after : List Char) (k m : Nat), chars input acc = .ok (cs, after) →
      input.foldl Nesting.next (Inside k m) = after.foldl Nesting.next (Outside k m) := by
  fun_induction chars input acc
  all_goals intro cs after k m h
  all_goals try (cases h; done)
  case case2 =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [List.foldl_cons, next_inside_quote]
  case case4 a b c d rest acc u hu _ ih =>
    rw [foldl_inside_hex hu]
    exact ih cs after k m h
  case case5 a b c d acc u hu _ _ e f g hh after' low hlow _ ih =>
    rw [foldl_inside_hex hu, foldl_inside_hex hlow]
    exact ih cs after k m h
  case case10 e rest acc _ c _ ih =>
    simp only [List.foldl_cons, next_escape]
    exact ih cs after k m h
  case case13 c rest acc hq _ hb _ ih =>
    by_cases hc : c = '\\'
    · cases rest with
      | nil => simp [chars] at h
      | cons e rest' => exact absurd (hb e rest' hc rfl) id
    · simp only [List.foldl_cons, next_inside hq hc]
      exact ih cs after k m h

theorem foldl_skipWs (input : List Char) (k m : Nat) :
    input.foldl Nesting.next (Outside k m) = (skipWs input).foldl Nesting.next (Outside k m) := by
  induction input with
  | nil => rfl
  | cons c rest ih =>
    simp only [skipWs]
    split
    · rename_i hws
      have hc : c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' ∧ c ≠ ']' ∧ c ≠ '}' := by
        simp only [isWs, Bool.or_eq_true, beq_iff_eq] at hws
        rcases hws with ((rfl | rfl) | rfl) | rfl <;> decide
      rw [List.foldl_cons, next_outside hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2, ih]
    · rfl

theorem foldl_plain_outside (cs : List Char) (h : ∀ c ∈ cs, c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' ∧ c ≠ ']' ∧ c ≠ '}')
    (k m : Nat) : cs.foldl Nesting.next (Outside k m) = Outside k m := by
  induction cs with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := h c (by simp)
    rw [List.foldl_cons, next_outside h1 h2 h3 h4 h5]
    exact ih (fun d hd => h d (by simp [hd]))

theorem span_loop_all (p : Char → Bool) : ∀ (l acc token rest : List Char),
    List.span.loop p l acc = (token, rest) → (∀ c ∈ acc, p c = true) → ∀ c ∈ token, p c = true
  | [], acc, token, rest, h, hacc => by
    simp only [List.span.loop, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    intro c hc
    exact hacc c (List.mem_reverse.mp hc)
  | a :: l, acc, token, rest, h, hacc => by
    simp only [List.span.loop] at h
    split at h
    · rename_i ha
      exact span_loop_all p l (a :: acc) token rest h (fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ha
        · exact hacc c hc)
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro c hc
      exact hacc c (List.mem_reverse.mp hc)

theorem numberChar_plain {c : Char} (h : isNumberChar c = true) :
    c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' ∧ c ≠ ']' ∧ c ≠ '}' := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rintro rfl; exact absurd h (by decide))

theorem foldl_number {input token rest : List Char} (h : input.span isNumberChar = (token, rest)) (k m : Nat) :
    input.foldl Nesting.next (Outside k m) = rest.foldl Nesting.next (Outside k m) := by
  have hall := span_loop_all isNumberChar input [] token rest h (fun _ hc => absurd hc List.not_mem_nil)
  rw [span_append _ _ _ _ h, List.foldl_append,
    foldl_plain_outside token (fun c hc => numberChar_plain (hall c hc))]

theorem depth_array (items : Array Value) : (Value.array items).depth = itemsDepth items.toList + 1 := by
  cases items
  rfl

theorem depth_table (ms : Array (String × Value)) : (Value.table ms).depth = membersDepth ms.toList + 1 := by
  cases ms
  rfl

theorem membersDepth_perm {l l' : List (String × Value)} (h : l.Perm l') : membersDepth l = membersDepth l' := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    obtain ⟨_, _⟩ := x
    simp only [membersDepth, ih]
  | swap x y l =>
    obtain ⟨_, _⟩ := x
    obtain ⟨_, _⟩ := y
    simp only [membersDepth]
    omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem table_depth {l : List (String × Value)} {t : Value} (h : table l = .ok t) : t.depth = membersDepth l + 1 := by
  unfold table at h
  dsimp only at h
  split at h
  · cases h
    rw [depth_table, List.toList_toArray, membersDepth_perm (List.mergeSort_perm _ _)]
  · cases h

theorem number_depth {token : List Char} {v : Value} (h : numberValue token = .ok v) : v.depth = 0 := by
  rcases numberValue_shape _ _ h with ⟨n, rfl⟩ | ⟨d, rfl⟩ <;> rfl

theorem foldl_word (w rest : List Char) (hw : ∀ c ∈ w, c ≠ '"' ∧ c ≠ '[' ∧ c ≠ '{' ∧ c ≠ ']' ∧ c ≠ '}')
    (k m : Nat) : (w ++ rest).foldl Nesting.next (Outside k m) = rest.foldl Nesting.next (Outside k m) := by
  rw [List.foldl_append, foldl_plain_outside w hw]

theorem nesting_reader (fuel : Nat) :
    (∀ (input : List Char) (v : Value) (rest : List Char), value fuel input = .ok (v, rest) →
      ∀ k m, k ≤ m → input.foldl Nesting.next (Outside k m) =
        rest.foldl Nesting.next (Outside k (max m (k + v.depth)))) ∧
    (∀ (input : List Char) (acc : Array Value) (v : Value) (rest : List Char),
      elements fuel input acc = .ok (v, rest) →
      ∃ new : List Value, v = .array ⟨acc.toList ++ new⟩ ∧ ∀ k m, k + 1 ≤ m →
        input.foldl Nesting.next (Outside (k + 1) m) =
          rest.foldl Nesting.next (Outside k (max m (k + 1 + itemsDepth new)))) ∧
    (∀ (input : List Char) (acc : Array (String × Value)) (v : Value) (rest : List Char),
      members fuel input acc = .ok (v, rest) →
      ∃ new : List (String × Value), v.depth = membersDepth (acc.toList ++ new) + 1 ∧ ∀ k m, k + 1 ≤ m →
        input.foldl Nesting.next (Outside (k + 1) m) =
          rest.foldl Nesting.next (Outside k (max m (k + 1 + membersDepth new)))) := by
  induction fuel with
  | zero => exact ⟨fun _ _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h), fun _ _ _ _ h => (nomatch h)⟩
  | succ fuel ih =>
    obtain ⟨ihV, ihE, ihM⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro input v rest h k m hkm
      unfold value at h
      split at h
      · cases h
        rw [show ('n' :: 'u' :: 'l' :: 'l' :: rest : List Char) = ['n', 'u', 'l', 'l'] ++ rest from rfl,
          foldl_word _ _ (by decide)]
        simp only [Value.depth, Nat.add_zero, Nat.max_eq_left hkm]
      · cases h
        rw [show ('t' :: 'r' :: 'u' :: 'e' :: rest : List Char) = ['t', 'r', 'u', 'e'] ++ rest from rfl,
          foldl_word _ _ (by decide)]
        simp only [Value.depth, Nat.add_zero, Nat.max_eq_left hkm]
      · cases h
        rw [show ('f' :: 'a' :: 'l' :: 's' :: 'e' :: rest : List Char) = ['f', 'a', 'l', 's', 'e'] ++ rest from rfl,
          foldl_word _ _ (by decide)]
        simp only [Value.depth, Nat.add_zero, Nat.max_eq_left hkm]
      · rename_i rest' 
        split at h
        · rename_i cs after hcs
          cases h
          rw [List.foldl_cons, next_outside_quote, foldl_chars _ _ _ _ k m hcs]
          simp only [Value.depth, Nat.add_zero, Nat.max_eq_left hkm]
        · cases h
      · rename_i rest'
        split at h
        · rename_i after hws
          cases h
          rw [List.foldl_cons, next_open (.inl rfl), foldl_skipWs, hws, List.foldl_cons, next_close (.inl rfl),
            depth_array]
          all_goals simp only [itemsDepth]
          all_goals (congr 2; omega)
        · obtain ⟨new, rfl, htr⟩ := ihE _ _ _ _ h
          rw [List.foldl_cons, next_open (.inl rfl), foldl_skipWs, htr k _ (by omega), depth_array]
          congr 2
          simp only [List.nil_append]
          omega
      · rename_i rest'
        split at h
        · rename_i after hws
          cases h
          rw [List.foldl_cons, next_open (.inr rfl), foldl_skipWs, hws, List.foldl_cons, next_close (.inr rfl),
            depth_table]
          all_goals simp only [membersDepth]
          all_goals (congr 2; omega)
        · obtain ⟨new, hdepth, htr⟩ := ihM _ _ _ _ h
          rw [List.foldl_cons, next_open (.inr rfl), foldl_skipWs, htr k _ (by omega), hdepth]
          congr 2
          simp only [List.nil_append]
          omega
      · split at h
        rename_i token rest' hspan
        split at h
        · cases h
        · split at h
          · rename_i w hw
            cases h
            rw [foldl_number hspan, number_depth hw, Nat.add_zero, Nat.max_eq_left hkm]
          · cases h
    · intro input acc v rest h
      unfold elements at h
      split at h
      · rename_i item rest1 hitem
        split at h
        · rename_i after hws
          obtain ⟨new, rfl, htr⟩ := ihE _ _ _ _ h
          refine ⟨item :: new, by simp, fun k m hkm => ?_⟩
          rw [ihV _ _ _ hitem (k + 1) m hkm, foldl_skipWs rest1, hws, List.foldl_cons,
            next_outside (by decide) (by decide) (by decide) (by decide) (by decide), foldl_skipWs after,
            htr k _ (by omega)]
          simp only [itemsDepth]
          congr 2
          omega
        · rename_i after hws
          cases h
          refine ⟨[item], by cases acc; simp [Array.push], fun k m hkm => ?_⟩
          rw [ihV _ _ _ hitem (k + 1) m hkm, foldl_skipWs rest1, hws, List.foldl_cons, next_close (.inl rfl)]
          simp only [itemsDepth]
          congr 2
          omega
        · cases h
      · cases h
    · intro input acc v rest h
      unfold members at h
      split at h
      · rename_i rest0
        split at h
        · rename_i key afterKey hkey
          split at h
          · rename_i afterColon hcolon
            split at h
            · rename_i item afterValue hitem
              split at h
              · rename_i after hws
                obtain ⟨new, hdepth, htr⟩ := ihM _ _ _ _ h
                refine ⟨(String.ofList key, item) :: new, by rw [hdepth]; simp, fun k m hkm => ?_⟩
                rw [List.foldl_cons, next_outside_quote, foldl_chars _ _ _ _ (k + 1) m hkey, foldl_skipWs afterKey,
                  hcolon, List.foldl_cons, next_outside (by decide) (by decide) (by decide) (by decide) (by decide),
                  foldl_skipWs afterColon, ihV _ _ _ hitem (k + 1) m hkm, foldl_skipWs afterValue, hws,
                  List.foldl_cons, next_outside (by decide) (by decide) (by decide) (by decide) (by decide),
                  foldl_skipWs after, htr k _ (by omega)]
                simp only [membersDepth]
                congr 2
                omega
              · rename_i after hws
                split at h
                · rename_i t ht
                  cases h
                  refine ⟨[(String.ofList key, item)], by rw [table_depth ht]; simp, fun k m hkm => ?_⟩
                  rw [List.foldl_cons, next_outside_quote, foldl_chars _ _ _ _ (k + 1) m hkey,
                    foldl_skipWs afterKey, hcolon, List.foldl_cons,
                    next_outside (by decide) (by decide) (by decide) (by decide) (by decide),
                    foldl_skipWs afterColon, ihV _ _ _ hitem (k + 1) m hkm, foldl_skipWs afterValue, hws,
                    List.foldl_cons, next_close (.inr rfl)]
                  simp only [membersDepth]
                  congr 2
                  omega
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h

theorem nesting_read {s : String} {v : Value} (h : read? s = some v) : nestingDepth s.toList = v.depth := by
  unfold read? Rfc8259.read at h
  split at h
  · rename_i w rest hw
    split at h
    · rename_i hrest
      simp only [Except.toOption, Option.some.injEq] at h
      subst h
      unfold nestingDepth
      show (s.toList.foldl Nesting.next (Outside 0 0)).deepest = w.depth
      rw [foldl_skipWs, (nesting_reader _).1 _ _ _ hw 0 0 (Nat.le_refl 0), foldl_skipWs, hrest]
      simp
    · cases h
  · cases h

end ExactJSON
