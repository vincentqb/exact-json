module

public import ExactJSON.Value

@[expose] public section

namespace ExactJSON.Example

structure Point where
  x : Int
  y : Int
  label? : Option String

inductive Shape where
  | dot
  | circle (radius : Nat)
  | rect (width height : Nat)
  | tagged : Nat → Shape
  | pair : Nat → String → Shape
  | scaled (factor : Nat) (inner : Shape)

structure Envelope where
  id : Nat
  note? : Option (Option String)
  shape : Shape

end ExactJSON.Example
