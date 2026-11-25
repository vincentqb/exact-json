module

public import ExactJSON.Value

@[expose] public section

namespace ExactJSON

namespace Value

mutual

def beq : Value → Value → Bool
  | .null, .null => true
  | .string a, .string b => a == b
  | .integer a, .integer b => a == b
  | .decimal a, .decimal b => a == b
  | .boolean a, .boolean b => a == b
  | .array ⟨as⟩, .array ⟨bs⟩ => beqItems as bs
  | .table ⟨as⟩, .table ⟨bs⟩ => beqMembers as bs
  | _, _ => false

def beqItems : List Value → List Value → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqItems as bs
  | _, _ => false

def beqMembers : List (String × Value) → List (String × Value) → Bool
  | [], [] => true
  | (k, a) :: as, (l, b) :: bs => k == l && beq a b && beqMembers as bs
  | _, _ => false

end

mutual

theorem eq_of_beq : (a b : Value) → Value.beq a b = true → a = b
  | .null, b, h => by cases b <;> simp_all [Value.beq]
  | .string x, b, h => by cases b <;> simp_all [Value.beq]
  | .integer x, b, h => by cases b <;> simp_all [Value.beq]
  | .decimal x, b, h => by cases b <;> simp_all [Value.beq]
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
  | .decimal _ => by simp [Value.beq]
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

theorem beq_eq_true_iff (a b : Value) : Value.beq a b = true ↔ a = b :=
  ⟨eq_of_beq a b, fun h => h ▸ beq_self a⟩

end Value

instance Value.instDecidableEq : DecidableEq Value := fun a b => decidable_of_iff _ (Value.beq_eq_true_iff a b)

end ExactJSON
