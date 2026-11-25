module

public import ExactJSON.Parse

@[expose] public section

namespace ExactJSON

structure Nesting where
  inString : Bool := false
  escaped : Bool := false
  depth : Nat := 0
  deepest : Nat := 0

def Nesting.next (n : Nesting) (c : Char) : Nesting :=
  if n.inString then
    if n.escaped then { n with escaped := false }
    else if c = '\\' then { n with escaped := true }
    else if c = '"' then { n with inString := false }
    else n
  else if c = '"' then { n with inString := true }
  else if c = '[' ∨ c = '{' then { n with depth := n.depth + 1, deepest := max n.deepest (n.depth + 1) }
  else if c = ']' ∨ c = '}' then { n with depth := n.depth - 1 }
  else n

def nestingDepth (cs : List Char) : Nat := (cs.foldl Nesting.next {}).deepest

def Value.read (sp : Spelling) (maxDepth : Nat) (b : ByteArray) : Except String Value :=
  match String.fromUTF8? b with
  | none => .error "not UTF-8"
  | some s =>
    if nestingDepth s.toList ≤ maxDepth then
      match sp with
      | .canonical => Value.parse s
      | .any => Value.readJson s
    else .error s!"nested deeper than {maxDepth}"

structure ReaderState where
  spelling : Spelling
  maxDepth : Nat
  bytes : ByteArray

abbrev Reader : Type := ReaderState

def Reader.start (sp : Spelling) (maxDepth : Nat) : Reader := ⟨sp, maxDepth, .empty⟩

def Reader.step (r : Reader) (x : UInt8) : Reader := ⟨r.spelling, r.maxDepth, r.bytes.push x⟩

def Reader.finish (r : Reader) : Except String Value := Value.read r.spelling r.maxDepth r.bytes

def lineStep (st : Array ByteArray × ByteArray) (x : UInt8) : Array ByteArray × ByteArray :=
  if x = 10 then (st.1.push st.2, .empty) else (st.1, st.2.push x)

def splitLines (b : ByteArray) : Option (Array ByteArray) :=
  let st := b.foldl lineStep (#[], .empty)
  if st.2.size = 0 then some st.1 else none

def readNumbered {α : Type} (read : ByteArray → Except String α) : Nat → List ByteArray → Except String (List α)
  | _, [] => .ok []
  | n, l :: ls =>
    match read l with
    | .ok v => (v :: ·) <$> readNumbered read (n + 1) ls
    | .error e => .error s!"line {n}: {e}"

def Value.readLines (sp : Spelling) (maxDepth : Nat) (b : ByteArray) : Except String (Array Value) :=
  match splitLines b with
  | none => .error "the last line has no line feed at its end"
  | some lines => List.toArray <$> readNumbered (Value.read sp maxDepth) 1 lines.toList

end ExactJSON
