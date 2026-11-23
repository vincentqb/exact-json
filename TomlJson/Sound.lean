module

public import TomlJson.Text
public import TomlJson.Codec

/-! # The reader is sound

Whatever the reader accepts is the canonical text of a valid value: reading `v` from `input`
with `rest` left means `input = render v ++ rest` and `v` is valid. So `Value.parse` needs no
check of what it read, and `decode` only compares values (`Value.beq a b = true ↔ a = b`).
-/

public section

namespace TomlJson

theorem keysIncreaseFrom_append (p : String) (l : List String) (k : String) :
    keysIncreaseFrom p (l ++ [k]) = true ↔ keysIncreaseFrom p l = true ∧ l.getLast?.getD p < k := by
  induction l generalizing p with
  | nil => simp [keysIncreaseFrom]
  | cons a l ih =>
    simp only [List.cons_append, keysIncreaseFrom, Bool.and_eq_true, decide_eq_true_eq, ih,
      List.getLast?_cons, Option.getD_some]
    exact and_assoc.symm

/-- Keys still increase after a key greater than the last. -/
theorem keysIncrease_push (l : List (String × Value)) (key : String) (item : Value)
    (hl : keysIncrease (l.map (·.1)) = true)
    (hlast : ∀ p w, l.getLast? = some (p, w) → p < key) :
    keysIncrease ((l ++ [(key, item)]).map (·.1)) = true := by
  match l, hl, hlast with
  | [], _, _ => simp [keysIncrease, keysIncreaseFrom]
  | a :: l', hl, hlast =>
    simp only [List.map_append, List.map_cons, List.map_nil, List.cons_append, keysIncrease] at hl ⊢
    refine (keysIncreaseFrom_append _ _ _).mpr ⟨hl, ?_⟩
    have keyLt : ∀ x : String × Value, (a :: l').getLast? = some x → x.1 < key := fun x hx => hlast x.1 x.2 hx
    cases hx : l'.getLast? with
    | none =>
      have := keyLt a (by simp [List.getLast?_cons, hx])
      simpa [List.getLast?_map, hx] using this
    | some x =>
      have := keyLt x (by simp [List.getLast?_cons, hx])
      simpa [List.getLast?_map, hx] using this

namespace Parser

theorem unescape_sound (e c : Char) (h : unescape e = some c) : (pushChar "" c).toList = ['\\', e] := by
  unfold unescape at h
  split at h <;> cases h <;> decide

theorem pushChar_plain (c : Char) (h1 : ¬(c == '"') = true) (h2 : ¬(c == '\\') = true) (h3 : ¬c.val < 32) :
    (pushChar "" c).toList = [c] := by
  have h4 : c.val ≥ 0x20 := by
    simp only [UInt32.not_lt] at h3
    exact h3
  simp only [pushChar, h1, h2, h4]
  simp

theorem string_step {acc str : String} {x : Char} {r rest : List Char}
    (ih : ∃ t, str.toList = (acc.push x).toList ++ t ∧ r = escapeList t ++ '"' :: rest) :
    ∃ t, str.toList = acc.toList ++ t ∧ (pushChar "" x).toList ++ r = escapeList t ++ '"' :: rest := by
  obtain ⟨t, h1, h2⟩ := ih
  exact ⟨x :: t, by simp [h1, String.toList_push], by simp [h2, escapeList_cons]⟩

/-- A string read is escaped characters and a closing quote. -/
theorem string_sound (input : List Char) (acc : String) (s0 : Nat) (str : String) (rest : List Char) (s : Nat)
    (h : string input acc s0 = .ok str rest s) :
    ∃ t, str.toList = acc.toList ++ t ∧ input = escapeList t ++ '"' :: rest := by
  fun_induction string input acc s0 <;> (try cases h)
  · rename_i c steps hq
    exact ⟨[], by simp, by simp [beq_iff_eq.mp hq, escapeList_nil]⟩
  · rename_i c acc steps _ h2 a b d e r written u _ _ char canonical hcan ih
    have hc : c = '\\' := beq_iff_eq.mp h2
    have hp : (pushChar "" char).toList = ['\\', 'u', a, b, d, e] := by
      have := beq_iff_eq.mp hcan
      simp only [canonical, written] at this
      rw [this, String.toList_ofList]
    have := string_step (ih h)
    rw [hp] at this
    rw [hc]
    exact this
  · rename_i c acc steps _ h2 e r _ u hu ih
    have hc : c = '\\' := beq_iff_eq.mp h2
    have := string_step (ih h)
    rw [unescape_sound e u hu] at this
    rw [hc]
    exact this
  · rename_i c rest' acc steps h1 h2 h3 ih
    have := string_step (ih h)
    rw [pushChar_plain c h1 h2 h3] at this
    exact this

theorem afterText_sound (k : Nat) (text input : List Char) (s0 : Nat) (rest : List Char) (s : Nat)
    (h : afterText k text input s0 = (some rest, s)) : input = text ++ rest ∧ text.length = k := by
  fun_induction afterText k text input s0 <;> (try cases h)
  · simp
  · rename_i c text d input steps hcd ih
    obtain ⟨h1, h2⟩ := ih h
    exact ⟨by rw [beq_iff_eq.mp hcd, h1]; rfl, by simp [h2]⟩

/-- The float of a decimal, when there is one, is finite. -/
theorem ofDecimal?_finite (negative : Bool) (m : Nat) (q : Int) (x : Float)
    (h : FloatText.ofDecimal? negative m q = some x) : finiteFloat x = true := by
  unfold FloatText.ofDecimal? at h
  simp only at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- The value of a number's parts is valid. -/
theorem Parts.value?_valid (p : Parts) (v : Value) (h : p.value? = some v) : v.isValid = true := by
  unfold Parts.value? at h
  split at h
  · simp only [Option.map_eq_some_iff] at h
    obtain ⟨x, hx, rfl⟩ := h
    simpa [Value.isValid] using ofDecimal?_finite _ _ _ _ hx
  · cases h
    rfl

/-- A number read is its own canonical text, and valid, whatever its parts were. -/
theorem numberAfter_sound (input : List Char) (scanned : Read Parts) (v : Value) (rest : List Char) (s : Nat)
    (h : numberAfter input scanned = .ok v rest s) : input = v.render.toList ++ rest ∧ v.isValid = true := by
  cases scanned with
  | error => simp [numberAfter] at h
  | ok p r s1 =>
    simp only [numberAfter] at h
    split at h
    · rename_i v' hv
      split at h
      · cases h
        exact ⟨(afterText_sound _ _ _ _ _ _ (by assumption)).1, Parts.value?_valid _ _ hv⟩
      · cases h
    · cases h

theorem number_sound (input : List Char) (s0 : Nat) (v : Value) (rest : List Char) (s : Nat)
    (h : number input s0 = .ok v rest s) : input = v.render.toList ++ rest ∧ v.isValid = true :=
  numberAfter_sound _ _ _ _ _ h

/-- What reading a value with `fuel` gives is a valid value and its text. -/
def ValueSound (fuel : Nat) : Prop :=
  ∀ (input : List Char) (s0 : Nat) (v : Value) (rest : List Char) (s : Nat),
    value fuel input s0 = .ok v rest s → input = v.render.toList ++ rest ∧ v.isValid = true

/-- What reading an array's items with `fuel` gives is valid items and their texts. -/
def ItemsSound (fuel : Nat) : Prop :=
  ∀ (input : List Char) (acc : Array Value) (s0 : Nat) (v : Value) (rest : List Char) (s : Nat),
    items fuel input acc s0 = .ok v rest s →
      ∃ ys, ys ≠ [] ∧ v = .array ⟨acc.toList ++ ys⟩ ∧ input = Value.itemsText ys ++ ']' :: rest ∧
        itemsValid ys = true

/-- What reading a table's members with `fuel` gives is valid members, in key order after those
read already, and their texts. -/
def MembersSound (fuel : Nat) : Prop :=
  ∀ (input : List Char) (acc : Array (String × Value)) (s0 : Nat) (v : Value) (rest : List Char) (s : Nat),
    members fuel input acc s0 = .ok v rest s → keysIncrease (acc.toList.map (·.1)) = true →
      ∃ ms, ms ≠ [] ∧ v = .table ⟨acc.toList ++ ms⟩ ∧ input = Value.membersText ms ++ '}' :: rest ∧
        membersValid ms = true ∧ keysIncrease ((acc.toList ++ ms).map (·.1)) = true

theorem array_push_eq {α : Type} (acc : Array α) (x : α) : acc.push x = ⟨acc.toList ++ [x]⟩ := by
  cases acc
  simp [Array.push]

theorem reader_sound (fuel : Nat) : ValueSound fuel ∧ ItemsSound fuel ∧ MembersSound fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro input s0 v rest s h
      simp [value] at h
    · intro input acc s0 v rest s h
      simp [items] at h
    · intro input acc s0 v rest s h
      simp [members] at h
  | succ fuel ih =>
    obtain ⟨ihValue, ihItems, ihMembers⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · intro input s0 v rest s h
      unfold value at h
      split at h
      · cases h
      · split at h
        · cases h
          rename_i rest' str after steps hstr
          obtain ⟨t, ht, hr⟩ := string_sound _ _ _ _ _ _ hstr
          simp only [String.toList_empty, List.nil_append] at ht
          subst ht
          refine ⟨?_, by simp [Value.isValid]⟩
          rw [Value.text_string, hr]
          simp
        · cases h
      · cases h
        have : (Value.render (.array #[])).toList = ['[', ']'] := by decide
        exact ⟨by rw [this]; rfl, by decide⟩
      · obtain ⟨ys, _, hv, hin, hvalid⟩ := ihItems _ _ _ _ _ _ h
        subst hv
        refine ⟨?_, by simpa [Value.isValid] using hvalid⟩
        simp only [List.nil_append]
        rw [Value.text_array, hin]
        simp
      · cases h
        have : (Value.render (.table #[])).toList = ['{', '}'] := by decide
        exact ⟨by rw [this]; rfl, by decide⟩
      · obtain ⟨ms, _, hv, hin, hvalid, hkeys⟩ := ihMembers _ _ _ _ _ _ h (by decide)
        subst hv
        simp only [List.nil_append] at hkeys ⊢
        refine ⟨?_, by simp [Value.isValid, hvalid, hkeys]⟩
        rw [Value.text_table, hin]
        simp
      · cases h
        exact ⟨by rw [Value.text_null]; rfl, by decide⟩
      · cases h
        exact ⟨by rw [Value.text_boolean]; rfl, by decide⟩
      · cases h
        exact ⟨by rw [Value.text_boolean]; rfl, by decide⟩
      · split at h
        · exact number_sound _ _ _ _ _ h
        · split at h <;> cases h
    · intro input acc s0 v rest s h
      unfold items at h
      split at h
      · rename_i item rest2 s1 hitem
        obtain ⟨ys, hne, hv, hin, hvalid⟩ := ihItems _ _ _ _ _ _ h
        obtain ⟨hinput, hitemValid⟩ := ihValue _ _ _ _ _ hitem
        refine ⟨item :: ys, by simp, ?_, ?_, ?_⟩
        · rw [hv, Array.toList_push, List.append_assoc]
          rfl
        · obtain ⟨w, ws, rfl⟩ := List.exists_cons_of_ne_nil hne
          rw [Value.itemsText_cons, hinput, hin]
          simp
        · simp [itemsValid, hitemValid, hvalid]
      · cases h
        rename_i _ item s1 hitem
        obtain ⟨hinput, hitemValid⟩ := ihValue _ _ _ _ _ hitem
        refine ⟨[item], by simp, by rw [array_push_eq], ?_, by simp [itemsValid, hitemValid]⟩
        rw [Value.itemsText_singleton, hinput]
      · cases h
      · cases h
    · intro input acc s0 v rest s h hkeys
      unfold members at h
      split at h
      · rename_i rest0
        split at h
        · cases h
        · rename_i key afterKey keySteps hkey
          obtain ⟨t, ht, hr⟩ := string_sound _ _ _ _ _ _ hkey
          simp only [String.toList_empty, List.nil_append] at ht
          subst ht
          simp only at h
          split at h
          · rename_i hordered
            -- the key comes after the last one read
            have hlast : ∀ p w, acc.toList.getLast? = some (p, w) → p < key := by
              intro p w hpw
              rw [Array.getLast?_toList] at hpw
              simp only [keyFollows, hpw] at hordered
              exact of_decide_eq_true hordered
            split at h
            · rename_i rest1
              split at h
              · rename_i item more s2 hitem
                obtain ⟨hinput, hitemValid⟩ := ihValue _ _ _ _ _ hitem
                have hk : keysIncrease ((acc.push (key, item)).toList.map (·.1)) = true := by
                  rw [Array.toList_push]
                  exact keysIncrease_push _ _ _ hkeys hlast
                obtain ⟨ms, hne, hv, hin, hvalid, hkeysAll⟩ := ihMembers _ _ _ _ _ _ h hk
                refine ⟨(key, item) :: ms, by simp, ?_, ?_, ?_, ?_⟩
                · rw [hv, Array.toList_push, List.append_assoc]
                  rfl
                · obtain ⟨m, ms', rfl⟩ := List.exists_cons_of_ne_nil hne
                  rw [hr, hinput, hin, Value.membersText_cons]
                  simp [Value.memberText]
                · simp [membersValid, hitemValid, hvalid]
                · rw [Array.toList_push, List.append_assoc] at hkeysAll
                  exact hkeysAll
              · cases h
                rename_i _ item s2 hitem
                obtain ⟨hinput, hitemValid⟩ := ihValue _ _ _ _ _ hitem
                refine ⟨[(key, item)], by simp, by rw [array_push_eq], ?_, by simp [membersValid, hitemValid],
                  keysIncrease_push _ _ _ hkeys hlast⟩
                rw [Value.membersText_singleton, hr, hinput]
                simp [Value.memberText]
              · cases h
              · cases h
            · cases h
          · cases h
      · cases h

end Parser

/-- What `Value.parse` reads is a valid value whose text is the text read. -/
theorem parse_sound (s : String) (v : Value) (h : Value.parse s = .ok v) : v.render = s ∧ v.isValid = true := by
  unfold Value.parse Value.parseCosted at h
  simp only at h
  split at h
  · rename_i v' steps hread
    simp only [Except.ok.injEq] at h
    subst h
    obtain ⟨hin, hvalid⟩ := (Parser.reader_sound _).1 _ _ _ _ _ hread
    refine ⟨?_, hvalid⟩
    rw [List.append_nil] at hin
    exact (String.toList_inj.mp hin).symm
  · simp [Parser.failAt] at h
  · simp [Parser.failAt] at h

namespace Value

mutual

/-- `Value.beq` is equality. -/
theorem eq_of_beq : (a b : Value) → Value.beq a b = true → a = b
  | .null, b, h => by cases b <;> simp_all [Value.beq]
  | .string x, b, h => by cases b <;> simp_all [Value.beq]
  | .integer x, b, h => by cases b <;> simp_all [Value.beq]
  | .float x, b, h => by cases b <;> simp_all [Value.beq]
  | .boolean x, b, h => by cases b <;> simp_all [Value.beq]
  | .array ⟨xs⟩, b, h => by
    rcases b with _ | _ | _ | _ | _ | ⟨⟨ys⟩⟩ | _ <;> simp [Value.beq] at h
    rw [eq_of_beqItems xs ys h]
  | .table ⟨xs⟩, b, h => by
    rcases b with _ | _ | _ | _ | _ | _ | ⟨⟨ys⟩⟩ <;> simp [Value.beq] at h
    rw [eq_of_beqMembers xs ys h]

theorem eq_of_beqItems : (xs ys : List Value) → Value.beqItems xs ys = true → xs = ys
  | [], ys, h => by cases ys <;> simp_all [Value.beqItems]
  | _ :: _, [], h => by simp [Value.beqItems] at h
  | x :: xs, y :: ys, h => by
    simp only [Value.beqItems, Bool.and_eq_true] at h
    rw [eq_of_beq x y h.1, eq_of_beqItems xs ys h.2]

theorem eq_of_beqMembers : (xs ys : List (String × Value)) → Value.beqMembers xs ys = true → xs = ys
  | [], ys, h => by cases ys <;> simp_all [Value.beqMembers]
  | _ :: _, [], h => by simp [Value.beqMembers] at h
  | (k, x) :: xs, (l, y) :: ys, h => by
    simp only [Value.beqMembers, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, eq_of_beq x y h.1.2, eq_of_beqMembers xs ys h.2]

end

mutual

theorem beq_self : (a : Value) → Value.beq a a = true
  | .null => rfl
  | .string _ => by simp [Value.beq]
  | .integer _ => by simp [Value.beq]
  | .float _ => by simp [Value.beq]
  | .boolean _ => by simp [Value.beq]
  | .array ⟨xs⟩ => by
    simp only [Value.beq]
    exact beqItems_self xs
  | .table ⟨xs⟩ => by
    simp only [Value.beq]
    exact beqMembers_self xs

theorem beqItems_self : (xs : List Value) → Value.beqItems xs xs = true
  | [] => rfl
  | x :: xs => by
    simp only [Value.beqItems, Bool.and_eq_true]
    exact ⟨beq_self x, beqItems_self xs⟩

theorem beqMembers_self : (xs : List (String × Value)) → Value.beqMembers xs xs = true
  | [] => rfl
  | (_, x) :: xs => by
    simp only [Value.beqMembers, Bool.and_eq_true, beq_self_eq_true, true_and]
    exact ⟨beq_self x, beqMembers_self xs⟩

end

/-- `Value.beq` is equality. -/
theorem beq_eq_true_iff (a b : Value) : Value.beq a b = true ↔ a = b :=
  ⟨eq_of_beq a b, fun h => h ▸ beq_self a⟩

end Value

end TomlJson
