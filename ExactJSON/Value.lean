module

public import Std.Data.ExtTreeMap
public import ExactJSON.Digits

public section

namespace ExactJSON

universe u

structure Decimal where
  negative : Bool
  digits : Nat
  exponent : Int
  normal : Decimal.Normal digits exponent := by decide
  deriving DecidableEq, Repr

instance : Inhabited Decimal := ⟨⟨false, 0, 0, by decide⟩⟩

namespace Decimal

@[expose] def normalize (negative : Bool) (m : Nat) (q : Int) : Decimal :=
  if h : m = 0 then ⟨negative, 0, 0, by decide⟩
  else ⟨negative, (strip m q).1, (strip m q).2, strip_normal m q (Nat.pos_of_ne_zero h)⟩

end Decimal

inductive Value where
  | null
  | string (s : String)
  | integer (n : Int)
  | decimal (d : Decimal)
  | boolean (b : Bool)
  | array (items : Array Value)
  | table (members : Array (String × Value))
  deriving Inhabited, Repr

@[expose] def keysIncreaseFrom (previous : String) : List String → Bool
  | [] => true
  | k :: rest => decide (previous < k) && keysIncreaseFrom k rest

@[expose] def keysIncrease : List String → Bool
  | [] => true
  | k :: rest => keysIncreaseFrom k rest

mutual

@[expose] def Value.isValid : Value → Bool
  | .null | .string _ | .integer _ | .boolean _ => true
  | .decimal _ => true
  | .array ⟨items⟩ => itemsValid items
  | .table ⟨members⟩ => keysIncrease (members.map (·.1)) && membersValid members

@[expose] def itemsValid : List Value → Bool
  | [] => true
  | v :: rest => v.isValid && itemsValid rest

@[expose] def membersValid : List (String × Value) → Bool
  | [] => true
  | (_, v) :: rest => v.isValid && membersValid rest

end

abbrev Value.Valid (v : Value) : Prop := v.isValid = true

@[expose] def Value.get? (v : Value) (key : String) : Option Value :=
  match v with
  | .table members => (members.find? (·.1 == key)).map (·.2)
  | _ => none

mutual

@[expose] def Value.depth : Value → Nat
  | .array ⟨items⟩ => itemsDepth items + 1
  | .table ⟨members⟩ => membersDepth members + 1
  | _ => 0

@[expose] def itemsDepth : List Value → Nat
  | [] => 0
  | v :: rest => max v.depth (itemsDepth rest)

@[expose] def membersDepth : List (String × Value) → Nat
  | [] => 0
  | (_, v) :: rest => max v.depth (membersDepth rest)

end

inductive Spelling where
  | canonical
  | any
  deriving DecidableEq, Repr

class ToValue (α : Type u) where
  toValue : α → Value

class FromValue (α : Type u) where
  fromValue? : Value → Except String α

export ToValue (toValue)
export FromValue (fromValue?)

class NotNull (α : Type u) [ToValue α] : Prop where
  toValue_ne_null : ∀ a : α, toValue a ≠ .null

class LawfulValue (α : Type u) [ToValue α] [FromValue α] : Prop where
  fromValue_toValue : ∀ a : α, fromValue? (toValue a) = .ok a
  toValue_valid : ∀ a : α, (toValue a).Valid

end ExactJSON
