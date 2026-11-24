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

#check_failure (encode (some (none : Option Nat)))
