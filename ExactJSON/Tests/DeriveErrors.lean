module

import ExactJSON
meta import ExactJSON

open ExactJSON

/--
error: `x` and `x?` would both be written under the key "x"
-/
#guard_msgs in
structure Twice where
  x : Nat
  x? : Option Nat
  deriving ToValue

/--
error: `x` and `x?` would both be written under the key "x"
-/
#guard_msgs in
inductive TwiceArgs where
  | c (x : Nat) (x? : Option Nat)
  deriving FromValue

mutual
inductive Even where
  | zero
  | succ (n : Odd)
inductive Odd where
  | succ (n : Even)
end

/--
error: deriving ExactJSON instances for mutual inductive types is not supported
-/
#guard_msgs in
deriving instance ToValue for Even

inductive Tree where
  | node (children : List Tree)

/--
error: deriving ExactJSON instances for nested inductive types is not supported: a constructor holds `Tree` inside
another type
-/
#guard_msgs in
deriving instance ToValue for Tree

inductive Vec : Nat → Type where
  | nil : Vec 0
  | cons {n : Nat} (head : Nat) (tail : Vec n) : Vec (n + 1)

/--
error: deriving ExactJSON instances for indexed families is not supported
-/
#guard_msgs in
deriving instance FromValue for Vec

structure Pos where
  n : Nat
  pos : 0 < n

/--
error: field `pos` is a proof, which JSON does not hold
-/
#guard_msgs in
deriving instance ToValue for Pos

structure Sized where
  n : Nat
  v : Fin n

/--
error: the type of field `v` depends on another field
-/
#guard_msgs in
deriving instance ToValue for Sized

inductive Fn where
  | mk (f : Nat → Fn)

/--
error: field `f` holds `Fn` other than as itself
-/
#guard_msgs in
deriving instance ToValue for Fn

structure Raw where
  v : Value
  deriving ToValue, FromValue

/--
error: failed to synthesize instance of type class
  LawfulValue Value

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
---
error: failed to synthesize instance of type class
  LawfulValue Value

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
deriving instance LawfulValue for Raw

#check_failure (encode (some (none : Option Nat)))
