module

public import ExactJSON.Codec
public meta import Lean.Syntax

/-! # `exactjson%`: values written as JSON in Lean source

```lean
#eval (exactjson% {
  "name": "run 1",
  "iters": 100,          -- an integer
  "time": 1.0,           -- a float: it keeps its point
  "note": null,
  "sizes": [1, 2, 3],
  "day": $(LocalDate.mk 2024 2 29)  -- `toValue`: "2024-02-29"
}).render
```

This is Lean syntax for building a `Value`, not part of the format; what it builds is written as
ordinary JSON. A number without a point or exponent is an integer, one with either is a float.
`$(e)` is `toValue e`. Keys are strings or identifiers (an identifier's name is the key) and are
put in order; a repeated key, or a float literal too large for binary64, is a compile error.
-/

public section

namespace ExactJSON

/-- The syntax of a `exactjson%` value. -/
declare_syntax_cat exactjson (behavior := symbol)
/-- `null`. -/
syntax "null" : exactjson
/-- `true`. -/
syntax "true" : exactjson
/-- `false`. -/
syntax "false" : exactjson
/-- A string. -/
syntax str : exactjson
/-- An integer, perhaps negative. -/
syntax "-"? num : exactjson
/-- A float, perhaps negative. -/
syntax "-"? scientific : exactjson
/-- An array. -/
syntax "[" exactjson,* "]" : exactjson
/-- A table key. -/
syntax exactjsonKey := ident <|> str
/-- A table member. -/
syntax exactjsonMember := exactjsonKey ": " exactjson
/-- A table. -/
syntax "{" exactjsonMember,* "}" : exactjson
/-- A `Value` written as JSON (see the module docstring). -/
syntax "exactjson% " exactjson : term

open Lean in
/-- Fail unless the float literal `x` is finite. -/
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
      -- the name as written: no macro scopes, no `«»`
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
