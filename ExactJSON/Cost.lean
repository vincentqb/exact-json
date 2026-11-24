module

public import ExactJSON.Sound

/-! # The reader's steps are linear in the text's length

Each part of the reader takes at most a fixed number of steps for each character it reads (two
for a string, four for a value), and an error at most as many for each character of the text it
was given; the steps are counted as `Value.parseCosted` documents. So `Value.parseCosted s` takes
at most `10 * (s.length + 1)` steps: one for each byte decoded (at most four a character), four
for each character read, and two for each character counted to place an error. The reader counts
the steps itself, so this bounds its count, not its running time.
-/

public section

namespace ExactJSON

theorem utf8ByteSize_ofList_le (l : List Char) : (String.ofList l).utf8ByteSize ≤ 4 * l.length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [String.ofList_cons, String.utf8ByteSize_append, String.utf8ByteSize_singleton]
    have := Char.utf8Size_le_four c
    simp only [List.length_cons]
    omega

theorem utf8ByteSize_le (s : String) : s.utf8ByteSize ≤ 4 * s.length := by
  have := utf8ByteSize_ofList_le s.toList
  rwa [String.ofList_toList, String.length_toList] at this

namespace Parser

/-- A reading of `input` that began with `s0` steps took at most `k` steps for each character it
read; or it failed within `input`, after at most `k` steps for each character of `input` and `e`
more. -/
def Within {α : Type} (k e : Nat) (input : List Char) (s0 : Nat) : Read α → Prop
  | .ok _ rest s => s0 ≤ s ∧ s + k * rest.length ≤ s0 + k * input.length
  | .error _ r s => s ≤ s0 + k * input.length + e ∧ r.length ≤ input.length

theorem Within.weaken {α : Type} {k e : Nat} {input input' : List Char} {s0 s0' : Nat} {r : Read α}
    (h : Within k e input' s0' r) (h1 : s0 ≤ s0') (h2 : s0' + k * input'.length ≤ s0 + k * input.length)
    (h3 : input'.length ≤ input.length) : Within k e input s0 r := by
  cases r with
  | ok a rest s =>
    simp only [Within] at h ⊢
    exact ⟨Nat.le_trans h1 h.1, Nat.le_trans h.2 h2⟩
  | error m r s =>
    simp only [Within] at h ⊢
    exact ⟨by omega, Nat.le_trans h.2 h3⟩

theorem string_within (input : List Char) (acc : String) (s0 : Nat) :
    Within 2 0 input s0 (string input acc s0) := by
  fun_induction string input acc s0
  all_goals first
    | (simp only [Within, List.length_cons, List.length_nil]; omega)
    | (refine Within.weaken (by assumption) ?_ ?_ ?_ <;> (try simp only [List.length_cons]) <;> omega)

/-- A scan from `p` of `input` that began with `s0` steps took a step for each character it read
and one more; or it failed within `input`, after a step for each character of `input`. -/
def ScanWithin (p : Parts) (input : List Char) (s0 : Nat) : Read Parts → Prop
  | .ok p' r s => s0 ≤ s ∧ s + p.length ≤ s0 + p'.length + 1 ∧ p.length ≤ p'.length ∧
      p'.length ≤ p.length + input.length ∧ r.length ≤ input.length
  | .error _ r s => s ≤ s0 + input.length ∧ r.length ≤ input.length

theorem read_length (p : Parts) (g : Grammar) (c : Char) : (p.read g c).length = p.length + 1 := by
  cases g <;> rfl

theorem finish_within (g : Grammar) (p : Parts) (input : List Char) (s0 s : Nat) (hs : s0 ≤ s)
    (hs' : s ≤ s0 + 1) (hin : s = s0 ∨ 1 ≤ input.length) :
    ScanWithin p input s0 (finish g p input s) := by
  unfold finish
  split <;> simp only [ScanWithin] <;> omega

theorem scan_within (g : Grammar) (p : Parts) (input : List Char) (s0 : Nat) :
    ScanWithin p input s0 (scan g p input s0) := by
  fun_induction scan g p input s0
  · exact finish_within _ _ _ _ _ (Nat.le_refl _) (by omega) (.inl rfl)
  · rename_i g p c rest steps g' _ ih
    revert ih
    generalize scan g' (p.read g' c) rest (steps + 1) = r
    intro ih
    cases r <;> simp only [ScanWithin, read_length, List.length_cons] at ih ⊢ <;> omega
  · exact finish_within _ _ _ _ _ (by omega) (by omega) (.inr (by simp))

/-- What the lenient grammar gives, within `input` and after a step for each character of it. -/
def ScanLenient (input : List Char) (s0 : Nat) : Read Parts → Prop
  | .ok _ r s => s ≤ s0 + input.length ∧ r.length ≤ input.length
  | .error _ r s => s ≤ s0 + input.length ∧ r.length ≤ input.length

theorem lenientScan_within (input : List Char) (s0 : Nat) : ScanLenient input s0 (lenientScan input s0) := by
  unfold lenientScan
  split
  · rename_i rest
    have h := scan_within .sign { negative := true, length := 1 } rest s0
    revert h
    generalize scan _ _ rest s0 = r
    intro h
    cases r <;> simp only [ScanWithin, ScanLenient, List.length_cons] at h ⊢ <;> omega
  · rename_i c rest _
    have h := scan_within .whole { digits := c.toNat - 48, length := 1 } rest s0
    revert h
    generalize scan _ _ rest s0 = r
    intro h
    cases r <;> simp only [ScanWithin, ScanLenient, List.length_cons] at h ⊢ <;> omega
  · simp [ScanLenient]

/-- The lenient grammar's error is within `input`, after a step for each character of it. -/
theorem lenientError_steps (input : List Char) (s0 : Nat) (m : String) (r : List Char) (s : Nat)
    (h : lenientError input s0 = .error m r s) : s ≤ s0 + input.length ∧ r.length ≤ input.length := by
  have hs := lenientScan_within input s0
  unfold lenientError at h
  cases hsc : lenientScan input s0 with
  | error m' r' s' =>
    rw [hsc] at h hs
    simp only [ScanLenient] at hs
    simp only [Read.error.injEq] at h
    obtain ⟨-, rfl, rfl⟩ := h
    exact hs
  | ok p r' s' =>
    rw [hsc] at h hs
    simp only [ScanLenient] at hs
    simp only at h
    split at h
    · split at h
      · simp only [Read.error.injEq] at h
        obtain ⟨-, rfl, rfl⟩ := h
        exact hs
      · split at h <;> (simp only [Read.error.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h; exact ⟨hs.1, by omega⟩)
    · split at h <;> (simp only [Read.error.injEq] at h; obtain ⟨-, rfl, rfl⟩ := h; exact ⟨hs.1, by omega⟩)

theorem numberValue_nil : ∃ e, Rfc8259.numberValue [] = .error e := ⟨_, rfl⟩

theorem number_within (input : List Char) (s0 : Nat) : Within 16 16 input s0 (number input s0) := by
  unfold number
  split
  rename_i token rest hspan
  have hin := span_append _ _ _ _ hspan
  have hl : input.length = token.length + rest.length := by rw [hin, List.length_append]
  simp only
  split
  · rename_i v hv
    have hne : token ≠ [] := by
      rintro rfl
      obtain ⟨e, he⟩ := numberValue_nil
      rw [he] at hv
      cases hv
    have hk : 1 ≤ token.length := List.length_pos_iff.mpr hne
    split
    · simp only [Within]
      omega
    · simp only [Within]
      omega
  · rename_i e _
    generalize hr : lenientError input (s0 + 7 * token.length + 7) = r
    cases r with
    | ok v rest' s => exact absurd hr (lenientError_ne_ok _ _ _ _ _)
    | error m r s =>
      have := lenientError_steps _ _ _ _ _ hr
      simp only [Within]
      omega

/-- Reading a value with `fuel` takes at most sixteen steps a character. -/
def ValueWithin (fuel : Nat) : Prop := ∀ input s0, Within 16 16 input s0 (value fuel input s0)

/-- Reading an array's items with `fuel` takes at most sixteen steps a character. -/
def ItemsWithin (fuel : Nat) : Prop := ∀ input acc s0, Within 16 16 input s0 (items fuel input acc s0)

/-- Reading a table's members with `fuel` takes at most sixteen steps a character. -/
def MembersWithin (fuel : Nat) : Prop := ∀ input acc s0, Within 16 16 input s0 (members fuel input acc s0)

theorem reader_within (fuel : Nat) : ValueWithin fuel ∧ ItemsWithin fuel ∧ MembersWithin fuel := by
  induction fuel with
  | zero =>
    refine ⟨fun input s0 => ?_, fun input acc s0 => ?_, fun input acc s0 => ?_⟩ <;>
      simp only [value, items, members, Within] <;> omega
  | succ fuel ih =>
    obtain ⟨ihValue, ihItems, ihMembers⟩ := ih
    refine ⟨fun input s0 => ?_, fun input acc s0 => ?_, fun input acc s0 => ?_⟩
    · unfold value
      split
      · simp only [Within]
        omega
      · rename_i rest
        have hs := string_within rest "" (s0 + 1)
        revert hs
        generalize string rest "" (s0 + 1) = r
        intro hs
        cases r <;> simp only [Within, List.length_cons] at hs ⊢ <;> omega
      · simp only [Within, List.length_cons]
        omega
      · rename_i rest _
        exact Within.weaken (ihItems rest #[] (s0 + 1)) (by omega) (by simp; omega) (by simp)
      · simp only [Within, List.length_cons]
        omega
      · rename_i rest _
        exact Within.weaken (ihMembers rest #[] (s0 + 1)) (by omega) (by simp; omega) (by simp)
      · simp only [Within, List.length_cons]
        omega
      · simp only [Within, List.length_cons]
        omega
      · simp only [Within, List.length_cons]
        omega
      · split
        · exact number_within _ _
        · split <;> simp only [Within, List.length_cons] <;> omega
    · unfold items
      have hv := ihValue input s0
      revert hv
      generalize value fuel input s0 = r
      intro hv
      split
      · rename_i item rest s1
        simp only [Within, List.length_cons] at hv
        exact Within.weaken (ihItems rest (acc.push item) (s1 + 1)) (by omega) (by omega) (by omega)
      · simp only [Within, List.length_cons] at hv ⊢
        omega
      · simp only [Within] at hv ⊢
        omega
      · simp only [Within] at hv ⊢
        omega
    · unfold members
      split
      · rename_i rest0
        have hs := string_within rest0 "" 0
        revert hs
        generalize string rest0 "" 0 = r
        intro hs
        cases r with
        | error m r ks =>
          simp only [Within, List.length_cons] at hs ⊢
          omega
        | ok key afterKey ks =>
          simp only [Within] at hs
          simp only
          split
          · split
            · rename_i rest1
              have hv := ihValue rest1 (s0 + 1 + 2 * ks + 1)
              revert hv
              generalize value fuel rest1 (s0 + 1 + 2 * ks + 1) = r
              intro hv
              simp only [List.length_cons] at hs
              split
              · rename_i item more s2
                simp only [Within, List.length_cons] at hv
                exact Within.weaken (ihMembers more (acc.push (key, item)) (s2 + 1)) (by omega)
                  (by simp only [List.length_cons]; omega) (by simp only [List.length_cons]; omega)
              · simp only [Within, List.length_cons] at hv ⊢
                omega
              · simp only [Within, List.length_cons] at hv ⊢
                omega
              · simp only [Within, List.length_cons] at hv ⊢
                omega
            · simp only [Within, List.length_cons] at hs ⊢
              omega
          · simp only [Within, List.length_cons]
            omega
      · simp only [Within]
        omega

end Parser

/-- `Value.parseCosted s` takes at most `22 * (s.length + 1)` steps. -/
theorem parseCosted_steps (s : String) : (Value.parseCosted s).steps ≤ 22 * (s.length + 1) := by
  have hB := utf8ByteSize_le s
  have hn : s.toList.length = s.length := String.length_toList
  have hv := (Parser.reader_within (2 * s.utf8ByteSize + 2)).1 s.toList s.utf8ByteSize
  unfold Value.parseCosted
  simp only
  revert hv
  generalize Parser.value (2 * s.utf8ByteSize + 2) s.toList s.utf8ByteSize = r
  intro hv
  split
  · simp only [Parser.Within, List.length_nil] at hv
    simp only
    omega
  · simp only [Parser.Within] at hv
    simp only [Parser.failAt]
    omega
  · simp only [Parser.Within] at hv
    simp only [Parser.failAt]
    omega

end ExactJSON
