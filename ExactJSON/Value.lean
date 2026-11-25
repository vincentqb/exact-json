module

public import Std.Data.ExtTreeMap

public section

namespace ExactJSON

universe u

structure Decimal where
  negative : Bool
  digits : Nat
  exponent : Int
  deriving DecidableEq, Repr, Inhabited

namespace Decimal

@[expose] def isNormal (d : Decimal) : Bool :=
  if d.digits = 0 then d.exponent == 0 else d.digits % 10 != 0

@[expose] def strip (m : Nat) (q : Int) : Nat × Int :=
  if h : 0 < m ∧ m % 10 = 0 then strip (m / 10) (q + 1) else (m, q)
termination_by m
decreasing_by omega

@[expose] def normalize (negative : Bool) (m : Nat) (q : Int) : Decimal :=
  if m = 0 then ⟨negative, 0, 0⟩ else ⟨negative, (strip m q).1, (strip m q).2⟩

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

@[expose] def finiteFloat (x : Float) : Bool :=
  (x.toBits.toNat / 2 ^ 52) % 2 ^ 11 != 2 ^ 11 - 1

@[expose] def keysIncreaseFrom (previous : String) : List String → Bool
  | [] => true
  | k :: rest => decide (previous < k) && keysIncreaseFrom k rest

@[expose] def keysIncrease : List String → Bool
  | [] => true
  | k :: rest => keysIncreaseFrom k rest

mutual

@[expose] def Value.isValid : Value → Bool
  | .null | .string _ | .integer _ | .boolean _ => true
  | .decimal d => d.isNormal
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
