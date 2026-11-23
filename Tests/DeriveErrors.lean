module

import TomlJson
meta import TomlJson

/-! Types the handler must refuse. -/

open TomlJson

/--
error: `x` and `x?` would both be written under the key "x"
-/
#guard_msgs in
structure Twice where
  /-- A value. -/
  x : Nat
  /-- The same key. -/
  x? : Option Nat
  deriving ToValue

/--
error: `x` and `x?` would both be written under the key "x"
-/
#guard_msgs in
inductive TwiceArgs where
  /-- Two arguments with one key. -/
  | c (x : Nat) (x? : Option Nat)
  deriving FromValue
