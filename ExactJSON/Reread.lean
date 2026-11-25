module

public import ExactJSON.Rfc8259
public import ExactJSON.Render

@[expose] public section

namespace ExactJSON

namespace Value

def rereadDecimal (d : Decimal) : Option Value :=
  match Rfc8259.numberValue d.text.toList with
  | .ok w => some w
  | .error _ => none

mutual

def reread : Value → Option Value
  | .null => some .null
  | .string s => some (.string s)
  | .integer n => some (.integer n)
  | .decimal d => rereadDecimal d
  | .boolean b => some (.boolean b)
  | .array ⟨items⟩ => (rereadItems items).map fun ys => .array ⟨ys⟩
  | .table ⟨members⟩ => (rereadMembers members).map fun ms => .table ⟨ms⟩

def rereadItems : List Value → Option (List Value)
  | [] => some []
  | v :: vs =>
    match reread v, rereadItems vs with
    | some w, some ws => some (w :: ws)
    | _, _ => none

def rereadMembers : List (String × Value) → Option (List (String × Value))
  | [] => some []
  | (k, v) :: ms =>
    match reread v, rereadMembers ms with
    | some w, some ws => some ((k, w) :: ws)
    | _, _ => none

end

end Value

end ExactJSON
