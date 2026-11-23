module

public import TomlJson.Class
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util

/-! # `deriving ToValue, FromValue`

The shapes are those of Lean's `deriving ToJson, FromJson`, but for `none` fields:

* a structure is a table of its fields; a field of type `Option α` is absent when `none`, and a
  field named `x?` is written under the key `x`;
* a constructor with no arguments is its name as a string: `"red"`;
* a constructor with named arguments is a one-key table holding a table of them, which follow the
  rules of fields: `{"circle":{"radius":1.0}}`;
* a constructor with one unnamed argument holds it directly: `{"some":3}`; with several unnamed
  arguments, an array of them: `{"pair":[1,2]}`.

Reading is strict: a key that is not a field is an error, and so is a missing key that is not an
`Option` field. Keys must differ (fields `x` and `x?` do not), which the handler checks; it writes
them in key order. A derived type is never written as `null`, so it gets `NotNull` too.

The handler is adapted from Lean's own `ToJson`/`FromJson` handler
(`Lean.Elab.Deriving.FromToJson`, Apache 2.0, Sebastian Ullrich and Dany Fabian).
-/

public section

namespace TomlJson.Derive

universe u

/-- A table of members already in key order. -/
def table (members : Array (String × Value)) : Value := .table members

/-- Check that every key of the table `v` is one of `keys`, for a type or constructor `name`. -/
def onlyKeys (name : String) (keys : Array String) (v : Value) : Except String Unit :=
  match v with
  | .table members =>
    match members.find? (!keys.contains ·.1) with
    | some (k, _) => .error s!"{name} has no field {pushString "" k}"
    | none => pure ()
  | _ => pure ()

/-- A constructor and its arguments: the one-key table `{name: payload}`. -/
def ctor (name : String) (payload : Value) : Value := .table #[(name, payload)]

/-- A constructor's name and, unless it was written as a bare string, its payload. -/
def tag? (v : Value) : Except String (String × Option Value) :=
  match v with
  | .string s => pure (s, none)
  | .table #[(k, payload)] => pure (k, some payload)
  | v => typeMismatch "a constructor: its name, or a table of one key" v

/-- The payload of a constructor that takes arguments. -/
def payload (name : String) : Option Value → Except String Value
  | some p => pure p
  | none => .error s!"constructor {name} takes arguments: expected a table {pushString "" name}: …"

/-- Check that a constructor with no arguments came as its bare name. -/
def noPayload (name : String) : Option Value → Except String Unit
  | none => pure ()
  | some _ => .error s!"constructor {name} takes no arguments: expected the string {pushString "" name}"

/-- The items of an array of exactly `n` items. -/
def items (n : Nat) : Value → Except String (Array Value)
  | .array xs => if xs.size == n then pure xs else typeMismatch s!"an array of {n} items" (.array xs)
  | v => typeMismatch s!"an array of {n} items" v

/-- Check that `v` is a table, for a structure named `name`. -/
def expectTable (name : String) (v : Value) : Except String Unit :=
  match v with
  | .table _ => pure ()
  | v => typeMismatch s!"a table ({name})" v

/-- The field `key` of a table, read by `read` (for a field of the type being derived). -/
def fieldWith {α : Type u} (read : Value → Except String α) (v : Value) (key : String) :
    Except String α :=
  match v.get? key with
  | some item => withContext key (read item)
  | none => .error s!"missing key {pushString "" key}"

end TomlJson.Derive

end

public meta section

namespace TomlJson.Derive
open Lean Elab Command Term Meta Parser.Term Lean.Elab.Deriving

/-- The key a field or argument named `n` is written under: its name, less a trailing `?`. -/
def fieldKey (n : Name) : CoreM String := do
  let .str .anonymous s := n.eraseMacroScopes | throwError "invalid field name {n}"
  return (s.dropEndWhile (· == '?')).copy

/-- The keys of some fields or named arguments, which must all differ: a field `x` and a field
`x?` would both be written under `x`. -/
def fieldKeys (names : Array Name) : CoreM (Array String) := do
  let keys ← names.mapM fieldKey
  for i in [0:keys.size] do
    for j in [i + 1:keys.size] do
      if keys[i]! == keys[j]! then
        throwError "`{names[i]!}` and `{names[j]!}` would both be written under the key {repr keys[i]!}"
  return keys

/-- The pattern-match alternatives over an inductive's constructors, with `rhs` given each
constructor, its bound arguments and their types, and their names when all are named. Taken from
Lean's `ToJson` handler. -/
def mkAlts (indVal : InductiveVal)
    (rhs : ConstructorVal → Array (Ident × Expr) → Option (Array Name) → TermElabM Term) :
    TermElabM (Array (TSyntax ``matchAlt)) := do
  let mut alts := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let alt ← forallTelescopeReducing ctorInfo.type fun xs _ => do
      let mut patterns := #[]
      for _ in *...indVal.numIndices do
        patterns := patterns.push (← `(_))
      let mut ctorArgs := #[]
      for _ in *...indVal.numParams do
        ctorArgs := ctorArgs.push (← `(_))
      let mut binders := #[]
      let mut userNames := #[]
      for i in *...ctorInfo.numFields do
        let x := xs[indVal.numParams + i]!
        let localDecl ← x.fvarId!.getDecl
        if !localDecl.userName.hasMacroScopes then
          userNames := userNames.push localDecl.userName
        let a := mkIdent (← mkFreshUserName `a)
        binders := binders.push (a, localDecl.type)
        ctorArgs := ctorArgs.push a
      patterns := patterns.push (← `(@$(mkIdent ctorInfo.name):ident $ctorArgs:term*))
      let rhs ← rhs ctorInfo binders (if userNames.size == binders.size then some userNames else none)
      `(matchAltExpr| | $[$patterns:term],* => $rhs:term)
    alts := alts.push alt
  return alts

/-- The body of `toValue` for a structure: a table of its fields. -/
def mkToValueStruct (header : Header) (indName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let target := mkIdent header.targetNames[0]!
  let keys ← fieldKeys fields
  -- In key order, so that the table needs no sorting when written.
  let sorted := (fields.zip keys).qsort (·.2 < ·.2)
  let mut members ← `(#[])
  for (field, key) in sorted do
    let key := Syntax.mkStrLit key
    members ← `(TomlJson.ToField.pushField $members $key ($target).$(mkIdent field))
  `(TomlJson.Derive.table $members)

/-- The body of `toValue` for an inductive type, by constructor. -/
def mkToValueInduct (ctx : Deriving.Context) (header : Header) (indName : Name) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let auxFun := mkIdent ctx.auxFunNames[0]!
  -- An argument of the type being derived is written by the function being defined.
  let write (x : Ident) (type : Expr) : TermElabM Term :=
    if type.isAppOf indVal.name then `($auxFun:ident $x:ident) else `(TomlJson.toValue $x:ident)
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts indVal fun ctor args userNames => do
    let name := Syntax.mkStrLit ctor.name.eraseMacroScopes.getString!
    match args, userNames with
    | #[], _ => `(TomlJson.Value.string $name)
    | #[(x, t)], none => `(TomlJson.Derive.ctor $name $(← write x t))
    | xs, none =>
      let xs ← xs.mapM fun (x, t) => write x t
      `(TomlJson.Derive.ctor $name (TomlJson.Value.array #[$[$xs],*]))
    | xs, some names =>
      let keys ← fieldKeys names
      let sorted := (xs.zip keys).qsort (·.2 < ·.2)
      let mut members ← `(#[])
      for ((x, t), key) in sorted do
        let key := Syntax.mkStrLit key
        if t.isAppOf indVal.name then
          members ← `(Array.push $members ($key, $auxFun:ident $x:ident))
        else
          members ← `(TomlJson.ToField.pushField $members $key $x:ident)
      `(TomlJson.Derive.ctor $name (TomlJson.Derive.table $members))
  `(match $[$discrs],* with $alts:matchAlt*)

/-- The body of `fromValue?` for a structure: each field from the table. -/
def mkFromValueStruct (indName : Name) (v : Ident) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let keys ← fieldKeys fields
  let getters ← keys.mapM fun key => do
    `(doElem| TomlJson.FromField.getField? $v $(Syntax.mkStrLit key))
  let fieldIds := fields.map mkIdent
  let typeName := Syntax.mkStrLit (privateToUserName indName.eraseMacroScopes).toString
  let keyLits := keys.map Syntax.mkStrLit
  `(do
    TomlJson.Derive.expectTable $typeName $v
    TomlJson.Derive.onlyKeys $typeName #[$[$keyLits],*] $v
    $[let $fieldIds:ident ← $getters]*
    return { $[$fieldIds:ident := $(id fieldIds)],* })

/-- The body of `fromValue?` for an inductive type, by constructor name. -/
def mkFromValueInduct (ctx : Deriving.Context) (indName : Name) (v : Ident) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let auxFun := mkIdent ctx.auxFunNames[0]!
  let mut names := #[]
  let mut rhss := #[]
  for ctorName in indVal.ctors do
    let ctorInfo ← getConstInfoCtor ctorName
    let nameStr := ctorName.eraseMacroScopes.getString!
    let name := Syntax.mkStrLit nameStr
    let rhs ← forallTelescopeReducing ctorInfo.type fun xs _ => do
      let mut binders := #[]
      let mut userNames := #[]
      for i in *...ctorInfo.numFields do
        let x := xs[indVal.numParams + i]!
        let localDecl ← x.fvarId!.getDecl
        if !localDecl.userName.hasMacroScopes then
          userNames := userNames.push localDecl.userName
        binders := binders.push (mkIdent (← mkFreshUserName `a), localDecl.type)
      let ids := binders.map (·.1)
      -- An argument of the type being derived is read by the function being defined.
      let read (type : Expr) : TermElabM Term :=
        if type.isAppOf indVal.name then `($auxFun:ident) else `(TomlJson.fromValue?)
      if binders.isEmpty then
        `(do TomlJson.Derive.noPayload $name payload; return $(mkIdent ctorName):ident)
      else if userNames.size == binders.size then
        let keys ← fieldKeys userNames
        let mut getters := #[]
        for (_, t) in binders, key in keys do
          let key := Syntax.mkStrLit key
          if t.isAppOf indVal.name then
            getters := getters.push (← `(doElem| TomlJson.Derive.fieldWith $auxFun:ident p $key))
          else
            getters := getters.push (← `(doElem| TomlJson.FromField.getField? p $key))
        let keyLits := keys.map Syntax.mkStrLit
        `(do
          let p ← TomlJson.Derive.payload $name payload
          TomlJson.Derive.expectTable $name p
          TomlJson.Derive.onlyKeys $name #[$[$keyLits],*] p
          $[let $ids:ident ← $getters]*
          return $(mkIdent ctorName):ident $ids*)
      else if h : binders.size = 1 then
        let r ← read binders[0].2
        let arg ← `($r p)
        `(do
          let p ← TomlJson.Derive.payload $name payload
          let $(ids[0]!):ident ← $arg:term
          return $(mkIdent ctorName):ident $ids*)
      else
        let mut getters := #[]
        for (_, t) in binders, i in [:binders.size] do
          let r ← read t
          let arg ← `($r ps[$(quote i)]!)
          let place := Syntax.mkStrLit s!"{nameStr}[{i}]"
          getters := getters.push (← `(doElem| TomlJson.withContext $place $arg))
        `(do
          let p ← TomlJson.Derive.payload $name payload
          let ps ← TomlJson.Derive.items $(quote binders.size) p
          $[let $ids:ident ← $getters]*
          return $(mkIdent ctorName):ident $ids*)
    names := names.push name
    rhss := rhss.push (← `(TomlJson.withContext $name $rhs))
  `(match TomlJson.Derive.tag? $v with
    | .error e => .error e
    | .ok (tag, payload) =>
      match tag with
      $[| $names => $rhss]*
      | other => .error s!"unknown constructor {TomlJson.pushString "" other}")

open TSyntax.Compat in
/-- Lean's `mkHeader`, with instance binders for the field class `field` too: a field whose type is
a parameter then follows the field rule for whatever the parameter is (an `Option` is a key that
may be absent). -/
def mkHeaderWithField (className field : Name) (arity : Nat) (indVal : InductiveVal) :
    TermElabM Header := do
  let header ← mkHeader className arity indVal
  let extra ← mkInstImplicitBinders field indVal header.argNames
  let n := header.binders.size - arity
  return { header with
    binders := header.binders.extract 0 n ++ extra.map (⟨·⟩) ++ header.binders.extract n header.binders.size }

open TSyntax.Compat in
/-- Lean's `mkInstanceCmds` for one type, with instance binders for the field class `field` too. -/
def mkInstanceWithField (ctx : Deriving.Context) (className field : Name) (typeName : Name) :
    TermElabM (Array Command) := do
  let mut instances := #[]
  for i in *...ctx.typeInfos.size do
    let indVal := ctx.typeInfos[i]!
    if indVal.name == typeName then
      let argNames ← mkInductArgNames indVal
      let binders ← mkImplicitBinders argNames
      let binders := binders ++ (← mkInstImplicitBinders className indVal argNames) ++
        (← mkInstImplicitBinders field indVal argNames)
      let indType ← mkInductiveApp indVal argNames
      let type ← `($(mkCIdent className) $indType)
      let val ← `(⟨$(mkIdent ctx.auxFunNames[i]!)⟩)
      instances := instances.push
        (← `(instance $(mkIdent ctx.instName):ident $binders:implicitBinder* : $type := $val))
  return instances

/-- The `toValue` function of each type in the mutual block. -/
def mkToValueFuns (ctx : Deriving.Context) : TermElabM Command := do
  let mut defs := #[]
  for i in *...ctx.typeInfos.size do
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeaderWithField ``ToValue ``ToField 1 indVal
    let auxFun := mkIdent ctx.auxFunNames[i]!
    let body ← Term.elabBinders header.binders fun _ => do
      let type ← Term.elabTerm header.targetType none
      let indName := type.getAppFn.constName!
      if isStructure (← getEnv) indName then mkToValueStruct header indName
      else mkToValueInduct ctx header indName
    if ctx.usePartial then
      let letDecls ← mkLocalInstanceLetDecls ctx ``ToValue header.argNames
      let body ← mkLet letDecls body
      defs := defs.push (← `(partial def $auxFun:ident $header.binders:bracketedBinder* : TomlJson.Value := $body:term))
    else
      defs := defs.push (← `(def $auxFun:ident $header.binders:bracketedBinder* : TomlJson.Value := $body:term))
  `(mutual $defs:command* end)

/-- The `fromValue?` function of each type in the mutual block. -/
def mkFromValueFuns (ctx : Deriving.Context) : TermElabM Command := do
  let mut defs := #[]
  for i in *...ctx.typeInfos.size do
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeaderWithField ``FromValue ``FromField 0 indVal
    -- A fresh name: a field may be called `value`.
    let v := mkIdent (← mkFreshUserName `value)
    let binders := header.binders.push (← `(bracketedBinderF|($v : TomlJson.Value)))
    let auxFun := mkIdent ctx.auxFunNames[i]!
    let body ← Term.elabBinders binders fun _ => do
      let type ← Term.elabTerm header.targetType none
      let indName := type.getAppFn.constName!
      if isStructure (← getEnv) indName then mkFromValueStruct indName v
      else mkFromValueInduct ctx indName v
    let resultType ← mkInductiveApp indVal header.argNames
    if ctx.usePartial || indVal.isRec then
      let letDecls ← mkLocalInstanceLetDecls ctx ``FromValue header.argNames
      let body ← mkLet letDecls body
      defs := defs.push (← `(partial def $auxFun:ident $binders:bracketedBinder* : Except String $resultType := $body:term))
    else
      defs := defs.push (← `(def $auxFun:ident $binders:bracketedBinder* : Except String $resultType := $body:term))
  `(mutual $defs:command* end)

/-- `NotNull T` for a type with derived `ToValue`, which writes a table or a string, never
`null`. -/
def mkNotNullInstance (declName : Name) : TermElabM Command := do
  let indVal ← getConstInfoInduct declName
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let indType ← mkInductiveApp indVal argNames
  `(instance $binders:implicitBinder* : TomlJson.NotNull $indType := ⟨⟩)

/-- The handler for `deriving ToValue`. -/
def mkToValueHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty || !(← declNames.allM isInductive) then return false
  for declName in declNames do
    let cmds ← liftTermElabM do
      let ctx ← mkContext ``ToValue "toValue" declName
      return #[← mkToValueFuns ctx] ++ (← mkInstanceWithField ctx ``ToValue ``ToField declName) ++
        #[← mkNotNullInstance declName]
    cmds.forM elabCommand
  return true

/-- The handler for `deriving FromValue`. -/
def mkFromValueHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty || !(← declNames.allM isInductive) then return false
  for declName in declNames do
    let cmds ← liftTermElabM do
      let ctx ← mkContext ``FromValue "fromValue" declName
      return #[← mkFromValueFuns ctx] ++ (← mkInstanceWithField ctx ``FromValue ``FromField declName)
    cmds.forM elabCommand
  return true

initialize
  registerDerivingHandler ``ToValue mkToValueHandler
  registerDerivingHandler ``FromValue mkFromValueHandler

end TomlJson.Derive

end
