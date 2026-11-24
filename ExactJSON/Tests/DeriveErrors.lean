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

/-- error: duplicate key "a" -/
#guard_msgs in
example : Value := exactjson% {"a": 1, b: 2, a: 3}

/--
error: this float is beyond the range of binary64, which has no infinity in JSON
-/
#guard_msgs in
example : Value := exactjson% [1.0e400]

#check_failure (encode (some (none : Option Nat)))
