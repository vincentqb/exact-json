module

public import TomlJson.Rfc8259
public import TomlJson.Render

/-! # Reading floats back

`Value.reread v` is `v` with each float read back from its canonical text by
`Rfc8259.numberValue`, or `none` when one is not. Whatever is read from a canonical text reads back
as itself, and RFC 8259 reads a valid value's text as its `reread`; so that every valid value is
read back from its text comes down to every finite float being read back from its own.
-/

@[expose] public section

namespace TomlJson

namespace Value

/-- What RFC 8259 reads in the canonical text of the float `x`, if anything. -/
def rereadFloat (x : Float) : Option Value :=
  match Rfc8259.numberValue (floatText x).toList with
  | .ok w => some w
  | .error _ => none

mutual

/-- `v` with each float read back from its canonical text. -/
def reread : Value → Option Value
  | .null => some .null
  | .string s => some (.string s)
  | .integer n => some (.integer n)
  | .float x => rereadFloat x
  | .boolean b => some (.boolean b)
  | .array ⟨items⟩ => (rereadItems items).map fun ys => .array ⟨ys⟩
  | .table ⟨members⟩ => (rereadMembers members).map fun ms => .table ⟨ms⟩

/-- Items, each read back. -/
def rereadItems : List Value → Option (List Value)
  | [] => some []
  | v :: vs =>
    match reread v, rereadItems vs with
    | some w, some ws => some (w :: ws)
    | _, _ => none

/-- Members, each value read back. -/
def rereadMembers : List (String × Value) → Option (List (String × Value))
  | [] => some []
  | (k, v) :: ms =>
    match reread v, rereadMembers ms with
    | some w, some ws => some ((k, w) :: ws)
    | _, _ => none

end

end Value

end TomlJson
