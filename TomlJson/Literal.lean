module

public import TomlJson.Codec
public meta import Lean.Syntax

/-! # `tomljson%`: values written as JSON in Lean source

```lean
#eval (tomljson% {
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

namespace TomlJson

/-- The syntax of a `tomljson%` value. -/
declare_syntax_cat tomljson (behavior := symbol)
/-- `null`. -/
syntax "null" : tomljson
/-- `true`. -/
syntax "true" : tomljson
/-- `false`. -/
syntax "false" : tomljson
/-- A string. -/
syntax str : tomljson
/-- An integer, perhaps negative. -/
syntax "-"? num : tomljson
/-- A float, perhaps negative. -/
syntax "-"? scientific : tomljson
/-- An array. -/
syntax "[" tomljson,* "]" : tomljson
/-- A table key. -/
syntax tomljsonKey := ident <|> str
/-- A table member. -/
syntax tomljsonMember := tomljsonKey ": " tomljson
/-- A table. -/
syntax "{" tomljsonMember,* "}" : tomljson
/-- A `Value` written as JSON (see the module docstring). -/
syntax "tomljson% " tomljson : term

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
  | `(tomljson% null) => `(TomlJson.Value.null)
  | `(tomljson% true) => `(TomlJson.Value.boolean Bool.true)
  | `(tomljson% false) => `(TomlJson.Value.boolean Bool.false)
  | `(tomljson% $s:str) => `(TomlJson.Value.string $s)
  | `(tomljson% $n:num) => `(TomlJson.Value.integer $n)
  | `(tomljson% -$n:num) => `(TomlJson.Value.integer (-$n))
  | `(tomljson% $x:scientific) => do
    checkFinite x
    `(TomlJson.Value.float $x)
  | `(tomljson% -$x:scientific) => do
    checkFinite x
    `(TomlJson.Value.float (-$x))
  | `(tomljson% [$[$xs],*]) => `(TomlJson.Value.array #[$[tomljson% $xs],*])
  | `(tomljson% {$[$ks:tomljsonKey : $vs:tomljson],*}) => do
    let keys : Array String ← ks.mapM fun
      -- the name as written: no macro scopes, no `«»`
      | `(tomljsonKey| $k:ident) => pure (k.getId.eraseMacroScopes.toString (escape := false))
      | `(tomljsonKey| $k:str) => pure k.getString
      | _ => Macro.throwUnsupported
    for i in [0:keys.size] do
      for j in [i + 1:keys.size] do
        if keys[i]! == keys[j]! then Macro.throwErrorAt ks[j]! s!"duplicate key {repr keys[j]!}"
    let members ← ((keys.zip vs).qsort (·.1 < ·.1)).mapM fun (k, v) => `(($(quote k), tomljson% $v))
    `(TomlJson.Value.table #[$[$members],*])
  | `(tomljson% $stx) =>
    if stx.raw.isAntiquot then
      let stx := ⟨stx.raw.getAntiquotTerm⟩
      `(TomlJson.toValue $stx)
    else Macro.throwUnsupported

end TomlJson
