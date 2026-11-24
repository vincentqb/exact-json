module

public import ExactJSON.Codec
public meta import Lean.Syntax

public section

namespace ExactJSON

declare_syntax_cat exactjson (behavior := symbol)
syntax "null" : exactjson
syntax "true" : exactjson
syntax "false" : exactjson
syntax str : exactjson
syntax "-"? num : exactjson
syntax "-"? scientific : exactjson
syntax "[" exactjson,* "]" : exactjson
syntax exactjsonKey := ident <|> str
syntax exactjsonMember := exactjsonKey ": " exactjson
syntax "{" exactjsonMember,* "}" : exactjson
syntax "exactjson% " exactjson : term

open Lean in
meta def checkFinite (x : TSyntax `scientific) : MacroM Unit := do
  match x.raw.isScientificLit? with
  | some (m, s, e) =>
    if (Float.ofScientific m s e).isInf then
      Macro.throwErrorAt x "this float is beyond the range of binary64, which has no infinity in JSON"
  | none => pure ()

open Lean in
macro_rules
  | `(exactjson% null) => `(ExactJSON.Value.null)
  | `(exactjson% true) => `(ExactJSON.Value.boolean Bool.true)
  | `(exactjson% false) => `(ExactJSON.Value.boolean Bool.false)
  | `(exactjson% $s:str) => `(ExactJSON.Value.string $s)
  | `(exactjson% $n:num) => `(ExactJSON.Value.integer $n)
  | `(exactjson% -$n:num) => `(ExactJSON.Value.integer (-$n))
  | `(exactjson% $x:scientific) => do
    checkFinite x
    `(ExactJSON.Value.float $x)
  | `(exactjson% -$x:scientific) => do
    checkFinite x
    `(ExactJSON.Value.float (-$x))
  | `(exactjson% [$[$xs],*]) => `(ExactJSON.Value.array #[$[exactjson% $xs],*])
  | `(exactjson% {$[$ks:exactjsonKey : $vs:exactjson],*}) => do
    let keys : Array String ← ks.mapM fun
      | `(exactjsonKey| $k:ident) => pure (k.getId.eraseMacroScopes.toString (escape := false))
      | `(exactjsonKey| $k:str) => pure k.getString
      | _ => Macro.throwUnsupported
    for i in [0:keys.size] do
      for j in [i + 1:keys.size] do
        if keys[i]! == keys[j]! then Macro.throwErrorAt ks[j]! s!"duplicate key {repr keys[j]!}"
    let members ← ((keys.zip vs).qsort (·.1 < ·.1)).mapM fun (k, v) => `(($(quote k), exactjson% $v))
    `(ExactJSON.Value.table #[$[$members],*])
  | `(exactjson% $stx) =>
    if stx.raw.isAntiquot then
      let stx := ⟨stx.raw.getAntiquotTerm⟩
      `(ExactJSON.toValue $stx)
    else Macro.throwUnsupported

end ExactJSON
