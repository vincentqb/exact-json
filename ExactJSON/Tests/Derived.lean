module

import ExactJSON
import ExactJSON.Solution
meta import ExactJSON

open ExactJSON

def decodeText {α : Type} [ToValue α] [FromValue α] (s : String) : Except String α := decode 10000 s.toUTF8

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

example (p : Pair Nat String) (h : (toValue p).depth ≤ 64) : decode 64 (encode p).toUTF8 = .ok p := decode_encode 64 p h
example (c : Chain (Pair Int Bool)) (h : (toValue c).depth ≤ 64) : decode 64 (encode c).toUTF8 = .ok c := decode_encode 64 c h
example (t : Triple) (h : (toValue t).depth ≤ 64) : decode 64 (encode t).toUTF8 = .ok t := decode_encode 64 t h
example (b : UBox (Array Op)) (h : (toValue b).depth ≤ 64) : decode 64 (encode b).toUTF8 = .ok b := decode_encode 64 b h
example (w : Wide) (h : (toValue w).depth ≤ 64) : decode 64 (encode w).toUTF8 = .ok w := decode_encode 64 w h
example (ws : Array Wide) (h : ∀ w ∈ ws, (toValue w).depth ≤ 64) :
    decodeLines 64 (encodeLines ws).toUTF8 = .ok ws := decodeLines_encode 64 ws h
example (e : Empty0) (h : (toValue e).depth ≤ 64) : decode 64 (encode e).toUTF8 = .ok e := decode_encode 64 e h

structure Tagged where
  labels : Std.ExtTreeMap String String
  counts? : Option (Std.ExtTreeMap String Nat)
  deriving ToValue, FromValue, LawfulValue

def labels (keys : List String) : Std.ExtTreeMap String String :=
  keys.foldl (fun m k => m.insert k (k ++ "!")) {}

example (t : Tagged) (h : (toValue t).depth ≤ 64) : decode 64 (encode t).toUTF8 = .ok t := decode_encode 64 t h
example : labels ["a", "b", "c", "d"] = labels ["c", "a", "d", "b"] := by decide

#guard encode ({ labels := labels ["team", "env"], counts? := none } : Tagged) ==
  "{\"labels\":{\"env\":\"env!\",\"team\":\"team!\"}}"
#guard !(decodeText "{\"labels\":{\"b\":\"x\",\"a\":\"y\"}}" : Except String Tagged).isOk

#guard encode ({} : Empty0) == "{}"
#guard encode ({ fst := 1, snd? := some "s" } : Pair Nat String) == "{\"fst\":1,\"snd\":\"s\"}"
#guard encode ({ fst := 1, snd? := none } : Pair Nat String) == "{\"fst\":1}"
#guard encode (Chain.link 1 (.link 2 .done)) == "{\"link\":{\"head\":1,\"rest\":{\"link\":{\"head\":2,\"rest\":\"done\"}}}}"
#guard encode ({ fst := 1, snd? := none, z := -3 } : Triple) == "{\"fst\":1,\"z\":-3}"
#guard encode (Op.call "f" #[1, 2] none) == "{\"call\":[\"f\",[1,2],null]}"
#guard encode (Op.neg (.lit 4)) == "{\"neg\":{\"lit\":4}}"
#guard encode wide == "{\"a01\":1,\"a02\":\"two\",\"a04\":true,\"a05\":[5,null],\"a06\":[\"x\"],\"a07\":\"é\",\"a08\":255,\"a09\":-9,\"a10\":0.1,\"a11\":[11,\"eleven\"],\"a12\":{\"add\":{\"lhs\":{\"lit\":1},\"rhs\":{\"neg\":{\"lit\":2}}}}}"
#guard ((decodeText (encode wide) : Except String Wide).map encode).toOption == some (encode wide)
#guard !(decodeText "{\"fst\":1,\"snd\":null}" : Except String (Pair Nat String)).isOk
#guard !(decodeText "{\"snd\":\"s\"}" : Except String (Pair Nat String)).isOk
#guard !(decodeText "{\"fst\":1,\"zz\":0}" : Except String (Pair Nat String)).isOk
#guard !(decodeText "{\"lit\":1,\"neg\":2}" : Except String Op).isOk
#guard !(decodeText "{\"call\":[\"f\",[1]]}" : Except String Op).isOk

namespace Domain

structure Req1 where
  a : Nat
  deriving ToValue, FromValue, LawfulValue

structure Req2 where
  a : Nat
  b : String
  deriving ToValue, FromValue, LawfulValue

structure ReqDefault where
  a : Nat
  b : Nat := 0
  deriving ToValue, FromValue, LawfulValue

structure ReqNested where
  inner : Req2
  items : List Req1
  pair : Req1 × Float
  map : Std.ExtTreeMap String Req1
  deriving ToValue, FromValue, LawfulValue

structure Opt1 where
  a? : Option Nat
  deriving ToValue, FromValue, LawfulValue

structure OptOpt where
  a? : Option (Option Nat)
  b : Bool
  deriving ToValue, FromValue, LawfulValue

structure ReqExt extends Req2 where
  c : Float
  deriving ToValue, FromValue, LawfulValue

structure ReqParam (α : Type) where
  a : α
  b : Nat
  deriving ToValue, FromValue, LawfulValue

inductive Shapes where
  | none0
  | single : Nat → Shapes
  | positional : Nat → String → Shapes
  | named1 (a : Nat)
  | named2 (a : Nat) (b : String)
  | namedOpt (a? : Option Nat)
  | namedMixed (a : Nat) (b? : Option String)
  deriving ToValue, FromValue, LawfulValue

inductive Tree where
  | leaf
  | wrap : Tree → Tree
  | pairOf : Tree → Tree → Tree
  | node (left : Tree) (value : Nat) (right : Tree)
  | only (child : Tree)
  | maybe (label? : Option String) (rest : Tree)
  deriving ToValue, FromValue, LawfulValue

example (x : Req1) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : Req2) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : ReqDefault) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : ReqNested) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : Opt1) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : OptOpt) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : ReqExt) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : ReqParam (Array Req1)) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : Shapes) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h
example (x : Tree) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h

#guard encode ({ a := 1 } : Req1) == "{\"a\":1}"
#guard encode ({ a := 1 } : ReqDefault) == "{\"a\":1,\"b\":0}"
#guard encode ({ a? := some none, b := true } : OptOpt) == "{\"a\":null,\"b\":true}"
#guard encode [Shapes.none0, .single 1, .positional 2 "p", .named1 3, .named2 4 "q", .namedOpt none,
    .namedMixed 5 (some "r")] ==
  "[\"none0\",{\"single\":1},{\"positional\":[2,\"p\"]},{\"named1\":{\"a\":3}},{\"named2\":{\"a\":4,\"b\":\"q\"}},{\"namedOpt\":{}},{\"namedMixed\":{\"a\":5,\"b\":\"r\"}}]"
#guard encode (Tree.node (.wrap .leaf) 7 (.maybe (some "m") (.only .leaf))) ==
  "{\"node\":{\"left\":{\"wrap\":\"leaf\"},\"right\":{\"maybe\":{\"label\":\"m\",\"rest\":{\"only\":{\"child\":\"leaf\"}}}},\"value\":7}}"
#guard !(decodeText "{\"a\":1,\"b\":null}" : Except String Req2).isOk
#guard !(decodeText "{\"b\":\"x\"}" : Except String Req2).isOk

structure Price where
  amount : Decimal
  cost? : Option Decimal
  deriving ToValue, FromValue, LawfulValue

example (x : Price) (h : (toValue x).depth ≤ 64) : decode 64 (encode x).toUTF8 = .ok x := decode_encode 64 x h

#guard encode ({ amount := ⟨false, 1999, -2, by decide⟩, cost? := none } : Price) == "{\"amount\":19.99}"

end Domain
