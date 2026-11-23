module

public import TomlJson.Sound

/-! # The reader's steps are linear in the text's length

Each part of the reader takes at most a fixed number of steps for each character it reads (two
for a string, four for a value), and an error at most as many for each character of the text it
was given; the steps are counted as `Value.parseCosted` documents. So `Value.parseCosted s` takes
at most `10 * (s.length + 1)` steps: one for each byte decoded (at most four a character), four
for each character read, and two for each character counted to place an error. The reader counts
the steps itself, so this bounds its count, not its running time.
-/

public section

namespace TomlJson

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
  | .ok p' _ s => s0 ≤ s ∧ s + p.length ≤ s0 + p'.length + 1 ∧ p.length ≤ p'.length ∧
      p'.length ≤ p.length + input.length
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

theorem afterText_steps (k : Nat) (text input : List Char) (s0 : Nat) :
    s0 ≤ (afterText k text input s0).2 ∧ (afterText k text input s0).2 ≤ s0 + k + 1 ∧
      ((afterText k text input s0).1.isSome = true → (afterText k text input s0).2 ≤ s0 + k) := by
  fun_induction afterText k text input s0
  · simp
  · rename_i k c text d input steps _ ih
    obtain ⟨h1, h2, h3⟩ := ih
    exact ⟨by omega, by omega, fun h => by have := h3 h; omega⟩
  · simp
  · simp

/-- What the start of the number reader gives `numberAfter`: the parts of at least one character
of `input`, after a step for each and one more; or an error within `input`. -/
def ScanNumber (input : List Char) (s0 : Nat) : Read Parts → Prop
  | .ok p _ s => s0 ≤ s ∧ s ≤ s0 + p.length + 1 ∧ 1 ≤ p.length ∧ p.length ≤ input.length
  | .error _ r s => s ≤ s0 + input.length ∧ r.length ≤ input.length

theorem scanNumber_of_within (p0 : Parts) (hp0 : p0.length = 1) (rest input : List Char)
    (hlen : input.length = rest.length + 1) (s0 : Nat) (r : Read Parts) (h : ScanWithin p0 rest (s0 + 1) r) :
    ScanNumber input s0 r := by
  cases r <;> simp only [ScanWithin, ScanNumber] at h ⊢ <;> omega

theorem numberAfter_within (input : List Char) (s0 : Nat) (scanned : Read Parts) (h : ScanNumber input s0 scanned) :
    Within 4 4 input s0 (numberAfter input scanned) := by
  cases scanned with
  | error m r s =>
    simp only [ScanNumber] at h
    simp only [numberAfter, Within]
    omega
  | ok p r s1 =>
    simp only [ScanNumber] at h
    simp only [numberAfter]
    split
    · rename_i v _
      have hsteps := afterText_steps p.length v.render.toList input s1
      split
      · rename_i rest s heq
        rw [heq] at hsteps
        obtain ⟨hin, hlen⟩ := afterText_sound _ _ _ _ _ _ heq
        have hl : input.length = p.length + rest.length := by rw [hin, List.length_append, hlen]
        simp only [Within, Option.isSome_some, forall_const] at hsteps ⊢
        omega
      · rename_i s heq
        rw [heq] at hsteps
        simp only [Within] at hsteps ⊢
        omega
    · simp only [Within]
      omega

theorem number_within (input : List Char) (s0 : Nat) : Within 4 4 input s0 (number input s0) := by
  unfold number
  apply numberAfter_within
  split
  · exact scanNumber_of_within _ rfl _ _ (by simp) _ _ (scan_within _ _ _ _)
  · exact scanNumber_of_within _ rfl _ _ (by simp) _ _ (scan_within _ _ _ _)
  · simp [ScanNumber]

/-- Reading a value with `fuel` takes at most four steps a character. -/
def ValueWithin (fuel : Nat) : Prop := ∀ input s0, Within 4 4 input s0 (value fuel input s0)

/-- Reading an array's items with `fuel` takes at most four steps a character. -/
def ItemsWithin (fuel : Nat) : Prop := ∀ input acc s0, Within 4 4 input s0 (items fuel input acc s0)

/-- Reading a table's members with `fuel` takes at most four steps a character. -/
def MembersWithin (fuel : Nat) : Prop := ∀ input acc s0, Within 4 4 input s0 (members fuel input acc s0)

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

/-- `Value.parseCosted s` takes at most `10 * (s.length + 1)` steps. -/
theorem parseCosted_steps (s : String) : (Value.parseCosted s).steps ≤ 10 * (s.length + 1) := by
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

end TomlJson
