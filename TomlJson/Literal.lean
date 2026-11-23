module

public import TomlJson.Class
public meta import Lean.Syntax

/-! # `tomljson%`: values written as JSON in Lean source

```lean
#eval (tomljson% {
  "name": "run 1",
  "iters": 100,          -- an integer
  "time": 1.0,           -- a float: it keeps its point
  "ok": true,
  "sizes": [1, 2, 3],
  "day": $(LocalDate.mk 2024 2 29)  -- `toValue`: "2024-02-29"
}).render
```

A literal without a point or exponent is an integer, one with either is a float (as in TOML and
in this format's text). There is no `null`. `$(e)` is `toValue e`. Keys are strings or
identifiers (an identifier's name is the key). The result is normalized (`Value.normalize`):
later keys win over earlier ones with the same name, and a float literal too large for binary64
is the string `"Infinity"`.
-/

public section

namespace TomlJson

/-- The syntax of a `tomljson%` value. -/
declare_syntax_cat tomljson (behavior := symbol)
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
/-- A `Value` written as JSON, not normalized: the expansion of `tomljson%`'s parts. -/
syntax "tomljson_raw% " tomljson : term

open Lean in
macro_rules
  | `(tomljson% $v) => `(TomlJson.Value.normalize (tomljson_raw% $v))
  | `(tomljson_raw% true) => `(TomlJson.Value.boolean Bool.true)
  | `(tomljson_raw% false) => `(TomlJson.Value.boolean Bool.false)
  | `(tomljson_raw% $s:str) => `(TomlJson.Value.string $s)
  | `(tomljson_raw% $n:num) => `(TomlJson.Value.integer $n)
  | `(tomljson_raw% -$n:num) => `(TomlJson.Value.integer (-$n))
  | `(tomljson_raw% $x:scientific) => `(TomlJson.Value.float $x)
  | `(tomljson_raw% -$x:scientific) => `(TomlJson.Value.float (-$x))
  | `(tomljson_raw% [$[$xs],*]) => `(TomlJson.Value.array #[$[tomljson_raw% $xs],*])
  | `(tomljson_raw% {$[$ks:tomljsonKey : $vs:tomljson],*}) => do
    let ks : Array (TSyntax `term) ← ks.mapM fun
      -- the name as written: no macro scopes, no `«»`
      | `(tomljsonKey| $k:ident) => pure (quote (k.getId.eraseMacroScopes.toString (escape := false)))
      | `(tomljsonKey| $k:str) => pure k
      | _ => Macro.throwUnsupported
    `(TomlJson.Value.table #[$[($ks, tomljson_raw% $vs)],*])
  | `(tomljson_raw% $stx) =>
    if stx.raw.isAntiquot then
      let stx := ⟨stx.raw.getAntiquotTerm⟩
      `(TomlJson.toValue $stx)
    else Macro.throwUnsupported

end TomlJson
