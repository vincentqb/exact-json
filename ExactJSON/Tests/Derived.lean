module

import ExactJSON
import ExactJSON.Solution
meta import ExactJSON

open ExactJSON

universe u

structure Empty0 where
  deriving ToValue, FromValue, LawfulValue

structure Pair (α β : Type) where
  fst : α
  snd? : Option β
  deriving ToValue, FromValue, LawfulValue

inductive Chain (α : Type) where
  | done
  | link (head : α) (rest : Chain α)
  deriving ToValue, FromValue, LawfulValue

structure Triple extends Pair Nat String where
  z : Int
  deriving ToValue, FromValue, LawfulValue

structure UBox (α : Type u) where
  x : α
  deriving ToValue, FromValue, LawfulValue

inductive Op where
  | lit : Nat → Op
  | neg : Op → Op
  | add (lhs rhs : Op)
  | call : String → Array Nat → Option Bool → Op
  | nop
  deriving ToValue, FromValue, LawfulValue

inductive Implicit where
  | mk {n : Nat} (tag : String)
  | pick (b : Bool) {k : Int}
  deriving ToValue, FromValue, LawfulValue

#guard encode (@Implicit.mk 3 "t") == "{\"mk\":{\"n\":3,\"tag\":\"t\"}}"
#guard encode (@Implicit.pick true 2) == "{\"pick\":{\"b\":true,\"k\":2}}"

structure Wide where
  a01 : Nat
  a02 : String
  a03? : Option Int
  a04 : Bool
  a05 : Array (Option Nat)
  a06? : Option (List String)
  a07 : Char
  a08 : UInt8
  a09 : Int64
  a10 : Float
  a11 : Nat × String
  a12 : Op
  deriving ToValue, FromValue, LawfulValue

def wide : Wide :=
  { a01 := 1, a02 := "two", a03? := none, a04 := true, a05 := #[some 5, none], a06? := some ["x"],
    a07 := 'é', a08 := 255, a09 := -9, a10 := 0.1, a11 := (11, "eleven"), a12 := .add (.lit 1) (.neg (.lit 2)) }

example (p : Pair Nat String) : decode (encode p) = .ok p := decode_encode p
example (c : Chain (Pair Int Bool)) : decode (encode c) = .ok c := decode_encode c
example (t : Triple) : decode (encode t) = .ok t := decode_encode t
example (b : UBox (Array Op)) : decode (encode b) = .ok b := decode_encode b
example (w : Wide) : decode (encode w) = .ok w := decode_encode w
example (ws : Array Wide) : decodeLines (encodeLines ws) = .ok ws := decodeLines_encode ws
example (e : Empty0) : decode (encode e) = .ok e := decode_encode e

#guard encode ({} : Empty0) == "{}"
#guard encode ({ fst := 1, snd? := some "s" } : Pair Nat String) == "{\"fst\":1,\"snd\":\"s\"}"
#guard encode ({ fst := 1, snd? := none } : Pair Nat String) == "{\"fst\":1}"
#guard encode (Chain.link 1 (.link 2 .done)) == "{\"link\":{\"head\":1,\"rest\":{\"link\":{\"head\":2,\"rest\":\"done\"}}}}"
#guard encode ({ fst := 1, snd? := none, z := -3 } : Triple) == "{\"fst\":1,\"z\":-3}"
#guard encode (Op.call "f" #[1, 2] none) == "{\"call\":[\"f\",[1,2],null]}"
#guard encode (Op.neg (.lit 4)) == "{\"neg\":{\"lit\":4}}"
#guard encode wide == "{\"a01\":1,\"a02\":\"two\",\"a04\":true,\"a05\":[5,null],\"a06\":[\"x\"],\"a07\":\"é\",\"a08\":255,\"a09\":-9,\"a10\":0.1,\"a11\":[11,\"eleven\"],\"a12\":{\"add\":{\"lhs\":{\"lit\":1},\"rhs\":{\"neg\":{\"lit\":2}}}}}"
#guard ((decode (encode wide) : Except String Wide).map encode).toOption == some (encode wide)
#guard !(decode "{\"fst\":1,\"snd\":null}" : Except String (Pair Nat String)).isOk
#guard !(decode "{\"snd\":\"s\"}" : Except String (Pair Nat String)).isOk
#guard !(decode "{\"fst\":1,\"zz\":0}" : Except String (Pair Nat String)).isOk
#guard !(decode "{\"lit\":1,\"neg\":2}" : Except String Op).isOk
#guard !(decode "{\"call\":[\"f\",[1]]}" : Except String Op).isOk
