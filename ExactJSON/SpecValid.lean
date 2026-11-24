module

public import ExactJSON.NumberValid

/-! # What RFC 8259 reads is a valid value

The reference reader `Rfc8259.read?` only gives valid values: tables with keys strictly increasing
(it sorts them and rejects a repeated key) and finite floats, at every depth.
-/

public section

namespace ExactJSON

namespace Rfc8259

/-- A table is valid when its keys increase and its values are valid. -/
theorem spec_isValid_table (ms : Array (String × Value)) :
    (Value.table ms).isValid = (keysIncrease (ms.toList.map (·.1)) && membersValid ms.toList) := by
  cases ms
  rfl

/-- An array is valid when its items are. -/
theorem spec_isValid_array (vs : Array Value) : (Value.array vs).isValid = itemsValid vs.toList := by
  cases vs
  rfl

/-- Members whose values are each valid are valid members. -/
theorem spec_membersValid (ms : List (String × Value)) (h : ∀ m ∈ ms, m.2.isValid = true) :
    membersValid ms = true := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    obtain ⟨k, v⟩ := m
    simp only [membersValid, Bool.and_eq_true]
    exact ⟨h (k, v) List.mem_cons_self, ih fun m hm => h m (List.mem_cons_of_mem _ hm)⟩

/-- Items that are each valid are valid items. -/
theorem spec_itemsValid (vs : List Value) (h : ∀ v ∈ vs, v.isValid = true) : itemsValid vs = true := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [itemsValid, Bool.and_eq_true]
    exact ⟨h v List.mem_cons_self, ih fun w hw => h w (List.mem_cons_of_mem _ hw)⟩

/-- Keys in order with no two neighbours equal increase from the first. -/
theorem spec_keysIncreaseFrom (a : String × Value) (l : List (String × Value))
    (hsorted : List.Pairwise (fun x y => decide (x.1 ≤ y.1) = true) (a :: l))
    (hdistinct : neighboursDistinct (a :: l) = true) :
    keysIncreaseFrom a.1 (l.map (·.1)) = true := by
  induction l generalizing a with
  | nil => rfl
  | cons b rest ih =>
    simp only [neighboursDistinct, Bool.and_eq_true, bne_iff_ne, ne_eq] at hdistinct
    have hab : a.1 ≤ b.1 := of_decide_eq_true (List.rel_of_pairwise_cons hsorted List.mem_cons_self)
    simp only [List.map_cons, keysIncreaseFrom, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨Std.lt_of_le_of_ne hab hdistinct.1, ih b (List.Pairwise.of_cons hsorted) hdistinct.2⟩

/-- Keys in order with no two neighbours equal increase. -/
theorem spec_keysIncrease (l : List (String × Value))
    (hsorted : List.Pairwise (fun x y => decide (x.1 ≤ y.1) = true) l)
    (hdistinct : neighboursDistinct l = true) : keysIncrease (l.map (·.1)) = true := by
  cases l with
  | nil => rfl
  | cons a l => exact spec_keysIncreaseFrom a l hsorted hdistinct

theorem table_valid (members : List (String × Value)) (t : Value)
    (hvalid : ∀ m ∈ members, m.2.isValid = true) (h : table members = .ok t) : t.isValid = true := by
  unfold table at h
  dsimp only at h
  split at h
  · rename_i hdistinct
    cases h
    have hsorted := List.pairwise_mergeSort (le := fun a b : String × Value => decide (a.1 ≤ b.1))
      (fun _ _ _ hab hbc => decide_eq_true (Std.le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc)))
      (fun _ _ => by simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Std.le_total) members
    rw [spec_isValid_table, List.toList_toArray, Bool.and_eq_true]
    exact ⟨spec_keysIncrease _ hsorted hdistinct,
      spec_membersValid _ fun m hm => hvalid m (List.mem_mergeSort.mp hm)⟩
  · cases h

/-- What the reader reads with `fuel` is valid: a value, and an array's elements or an object's
members after valid ones read already. -/
theorem spec_reader_valid (fuel : Nat) :
    (∀ (input : List Char) (v : Value) (rest : List Char),
      value fuel input = .ok (v, rest) → v.isValid = true) ∧
    (∀ (input : List Char) (acc : Array Value) (v : Value) (rest : List Char),
      (∀ x ∈ acc.toList, x.isValid = true) → elements fuel input acc = .ok (v, rest) → v.isValid = true) ∧
    (∀ (input : List Char) (acc : Array (String × Value)) (v : Value) (rest : List Char),
      (∀ m ∈ acc.toList, m.2.isValid = true) → members fuel input acc = .ok (v, rest) → v.isValid = true) := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro input v rest h
      exact nomatch h
    · intro input acc v rest _ h
      exact nomatch h
    · intro input acc v rest _ h
      exact nomatch h
  | succ fuel ih =>
    obtain ⟨ihValue, ihElements, ihMembers⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro input v rest h
      unfold value at h
      split at h
      · cases h
        rfl
      · cases h
        rfl
      · cases h
        rfl
      · split at h
        · cases h
          rfl
        · cases h
      · split at h
        · cases h
          rfl
        · exact ihElements _ _ _ _ (fun _ hx => absurd hx List.not_mem_nil) h
      · split at h
        · cases h
          rfl
        · exact ihMembers _ _ _ _ (fun _ hm => absurd hm List.not_mem_nil) h
      · split at h
        split at h
        · cases h
        · split at h
          · rename_i hnumber
            cases h
            exact numberValue_valid _ _ hnumber
          · cases h
    · intro input acc v rest hacc h
      unfold elements at h
      split at h
      · rename_i _ item _ hitem
        have hacc' : ∀ x ∈ (acc.push item).toList, x.isValid = true := by
          intro x hx
          rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
          rcases hx with hx | rfl
          · exact hacc x hx
          · exact ihValue _ _ _ hitem
        split at h
        · exact ihElements _ _ _ _ hacc' h
        · cases h
          rw [spec_isValid_array]
          exact spec_itemsValid _ hacc'
        · cases h
      · cases h
    · intro input acc v rest hacc h
      unfold members at h
      split at h
      · split at h
        · rename_i _ key _ _
          split at h
          · split at h
            · rename_i _ item _ hitem
              have hacc' : ∀ m ∈ (acc.push (String.ofList key, item)).toList, m.2.isValid = true := by
                intro m hm
                rw [Array.toList_push, List.mem_append, List.mem_singleton] at hm
                rcases hm with hm | rfl
                · exact hacc m hm
                · exact ihValue _ _ _ hitem
              split at h
              · exact ihMembers _ _ _ _ hacc' h
              · split at h
                · rename_i htable
                  cases h
                  exact table_valid _ _ hacc' htable
                · cases h
              · cases h
            · cases h
          · cases h
        · cases h
      · cases h

theorem value_valid (fuel : Nat) (input : List Char) (v : Value) (rest : List Char)
    (h : value fuel input = .ok (v, rest)) : v.isValid = true := by
  exact (spec_reader_valid fuel).1 input v rest h

theorem read?_valid (s : String) (v : Value) (h : read? s = some v) : v.isValid = true := by
  unfold read? read at h
  split at h
  · rename_i _ w _ hw
    split at h
    · cases h
      exact value_valid _ _ _ _ hw
    · cases h
  · cases h

end Rfc8259

end ExactJSON
