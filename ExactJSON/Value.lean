module

public section

/-!
# The vocabulary of the challenge

`Value` is the untyped form of a canonical text: JSON whose numbers are integers or binary64
floats. `Value.Valid` says which values have a canonical text. `ToValue` and `FromValue` say how
a Lean type is written as a value and read back. `Costed` is a result with the steps taken to
compute it, as the computation counts them.
-/

namespace ExactJSON

universe u

inductive Value where
  | null
  | string (s : String)
  | integer (n : Int)
  | float (x : Float)
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
  | .float x => finiteFloat x
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

structure Costed (α : Type u) where
  value : α
  steps : Nat

class ToValue (α : Type u) where
  toValue : α → Value

class FromValue (α : Type u) where
  fromValue? : Value → Except String α

export ToValue (toValue)
export FromValue (fromValue?)

end ExactJSON
