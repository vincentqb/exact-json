module

public import ExactJSON.Codec
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util

@[expose] public section

namespace ExactJSON.Derive

universe u

def table (members : Array (String × Value)) : Value := .table members

def onlyKeys (name : String) (keys : Array String) (v : Value) : Except String Unit :=
  match v with
  | .table members =>
    match members.find? (!keys.contains ·.1) with
    | some (k, _) => .error s!"{name} has no field {pushString "" k}"
    | none => pure ()
  | _ => pure ()

def ctor (name : String) (payload : Value) : Value := .table #[(name, payload)]

def tag? (v : Value) : Except String (String × Option Value) :=
  match v with
  | .string s => pure (s, none)
  | .table #[(k, payload)] => pure (k, some payload)
  | v => typeMismatch "a constructor: its name, or a table of one key" v

def payload (name : String) : Option Value → Except String Value
  | some p => pure p
  | none => .error s!"constructor {name} takes arguments: expected a table {pushString "" name}: …"

def noPayload (name : String) : Option Value → Except String Unit
  | none => pure ()
  | some _ => .error s!"constructor {name} takes no arguments: expected the string {pushString "" name}"

def items (n : Nat) : Value → Except String (Array Value)
  | .array xs => if xs.size == n then pure xs else typeMismatch s!"an array of {n} items" (.array xs)
  | v => typeMismatch s!"an array of {n} items" v

def expectTable (name : String) (v : Value) : Except String Unit :=
  match v with
  | .table _ => pure ()
  | v => typeMismatch s!"a table ({name})" v

def fieldWith {α : Type u} (read : Value → Except String α) (v : Value) (key : String) :
    Except String α :=
  match v.get? key with
  | some item => withContext key (read item)
  | none => .error s!"missing key {pushString "" key}"

mutual

def depth : Value → Nat
  | .array ⟨items⟩ => depthItems items + 1
  | .table ⟨members⟩ => depthMembers members + 1
  | _ => 0

def depthItems : List Value → Nat
  | [] => 0
  | v :: rest => max (depth v) (depthItems rest)

def depthMembers : List (String × Value) → Nat
  | [] => 0
  | (_, v) :: rest => max (depth v) (depthMembers rest)

end

def fuel {α : Type u} (step : (Value → Except String α) → Value → Except String α) :
    Nat → Value → Except String α
  | 0, _ => .error "decoding recursed deeper than the value"
  | n + 1, v => step (fuel step n) v

def fix {α : Type u} (step : (Value → Except String α) → Value → Except String α) (v : Value) :
    Except String α :=
  fuel step (depth v + 1) v

end ExactJSON.Derive

end

public meta section

namespace ExactJSON.Derive
open Lean Elab Command Term Meta Parser.Term Lean.Elab.Deriving

def fieldKey (n : Name) : CoreM String := do
  let .str .anonymous s := n.eraseMacroScopes | throwError "invalid field name {n}"
  return (s.dropEndWhile (· == '?')).copy

def fieldKeys (names : Array Name) : CoreM (Array String) := do
  let keys ← names.mapM fieldKey
  for i in [0:keys.size] do
    for j in [i + 1:keys.size] do
      if keys[i]! == keys[j]! then
        throwError "`{names[i]!}` and `{names[j]!}` would both be written under the key {repr keys[i]!}"
  return keys

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

def mkToValueStruct (header : Header) (indName : Name) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let target := mkIdent header.targetNames[0]!
  let keys ← fieldKeys fields
  let sorted := (fields.zip keys).qsort (·.2 < ·.2)
  let mut members ← `(#[])
  for (field, key) in sorted do
    let key := Syntax.mkStrLit key
    members ← `(ExactJSON.ToField.pushField $members $key ($target).$(mkIdent field))
  `(ExactJSON.Derive.table $members)

def mkToValueInduct (ctx : Deriving.Context) (header : Header) (indName : Name) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
  let auxFun := mkIdent ctx.auxFunNames[0]!
  let write (x : Ident) (type : Expr) : TermElabM Term :=
    if type.isAppOf indVal.name then `($auxFun:ident $x:ident) else `(ExactJSON.toValue $x:ident)
  let discrs ← mkDiscrs header indVal
  let alts ← mkAlts indVal fun ctor args userNames => do
    let name := Syntax.mkStrLit ctor.name.eraseMacroScopes.getString!
    match args, userNames with
    | #[], _ => `(ExactJSON.Value.string $name)
    | #[(x, t)], none => `(ExactJSON.Derive.ctor $name $(← write x t))
    | xs, none =>
      let xs ← xs.mapM fun (x, t) => write x t
      `(ExactJSON.Derive.ctor $name (ExactJSON.Value.array #[$[$xs],*]))
    | xs, some names =>
      let keys ← fieldKeys names
      let sorted := (xs.zip keys).qsort (·.2 < ·.2)
      let mut members ← `(#[])
      for ((x, t), key) in sorted do
        let key := Syntax.mkStrLit key
        if t.isAppOf indVal.name then
          members ← `(Array.push $members ($key, $auxFun:ident $x:ident))
        else
          members ← `(ExactJSON.ToField.pushField $members $key $x:ident)
      `(ExactJSON.Derive.ctor $name (ExactJSON.Derive.table $members))
  `(match $[$discrs],* with $alts:matchAlt*)

def mkFromValueStruct (indName : Name) (v : Ident) : TermElabM Term := do
  let fields := getStructureFieldsFlattened (← getEnv) indName (includeSubobjectFields := false)
  let keys ← fieldKeys fields
  let getters ← keys.mapM fun key => do
    `(doElem| ExactJSON.FromField.getField? $v $(Syntax.mkStrLit key))
  let fieldIds := fields.map mkIdent
  let typeName := Syntax.mkStrLit (privateToUserName indName.eraseMacroScopes).toString
  let keyLits := keys.map Syntax.mkStrLit
  `(do
    ExactJSON.Derive.expectTable $typeName $v
    ExactJSON.Derive.onlyKeys $typeName #[$[$keyLits],*] $v
    $[let $fieldIds:ident ← $getters]*
    return { $[$fieldIds:ident := $(id fieldIds)],* })

def mkFromValueInduct (recur : Ident) (indName : Name) (v : Ident) : TermElabM Term := do
  let indVal ← getConstInfoInduct indName
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
      let read (type : Expr) : TermElabM Term :=
        if type.isAppOf indVal.name then `($recur:ident) else `(ExactJSON.fromValue?)
      if binders.isEmpty then
        `(do ExactJSON.Derive.noPayload $name payload; return $(mkIdent ctorName):ident)
      else if userNames.size == binders.size then
        let keys ← fieldKeys userNames
        let mut getters := #[]
        for (_, t) in binders, key in keys do
          let key := Syntax.mkStrLit key
          if t.isAppOf indVal.name then
            getters := getters.push (← `(doElem| ExactJSON.Derive.fieldWith $recur:ident p $key))
          else
            getters := getters.push (← `(doElem| ExactJSON.FromField.getField? p $key))
        let keyLits := keys.map Syntax.mkStrLit
        `(do
          let p ← ExactJSON.Derive.payload $name payload
          ExactJSON.Derive.expectTable $name p
          ExactJSON.Derive.onlyKeys $name #[$[$keyLits],*] p
          $[let $ids:ident ← $getters]*
          return $(mkIdent ctorName):ident $ids*)
      else if h : binders.size = 1 then
        let r ← read binders[0].2
        let arg ← `($r p)
        `(do
          let p ← ExactJSON.Derive.payload $name payload
          let $(ids[0]!):ident ← $arg:term
          return $(mkIdent ctorName):ident $ids*)
      else
        let mut getters := #[]
        for (_, t) in binders, i in [:binders.size] do
          let r ← read t
          let arg ← `($r ps[$(quote i)]!)
          let place := Syntax.mkStrLit s!"{nameStr}[{i}]"
          getters := getters.push (← `(doElem| ExactJSON.withContext $place $arg))
        `(do
          let p ← ExactJSON.Derive.payload $name payload
          let ps ← ExactJSON.Derive.items $(quote binders.size) p
          $[let $ids:ident ← $getters]*
          return $(mkIdent ctorName):ident $ids*)
    names := names.push name
    rhss := rhss.push (← `(ExactJSON.withContext $name $rhs))
  `(match ExactJSON.Derive.tag? $v with
    | .error e => .error e
    | .ok (tag, payload) =>
      match tag with
      $[| $names => $rhss]*
      | other => .error s!"unknown constructor {ExactJSON.pushString "" other}")

open TSyntax.Compat in
def mkHeaderWithField (className field : Name) (arity : Nat) (indVal : InductiveVal) :
    TermElabM Header := do
  let header ← mkHeader className arity indVal
  let extra ← mkInstImplicitBinders field indVal header.argNames
  let n := header.binders.size - arity
  return { header with
    binders := header.binders.extract 0 n ++ extra.map (⟨·⟩) ++ header.binders.extract n header.binders.size }

open TSyntax.Compat in
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
      defs := defs.push (← `(partial def $auxFun:ident $header.binders:bracketedBinder* : ExactJSON.Value := $body:term))
    else
      defs := defs.push (← `(def $auxFun:ident $header.binders:bracketedBinder* : ExactJSON.Value := $body:term))
  `(mutual $defs:command* end)

def mkFromValueFuns (ctx : Deriving.Context) : TermElabM Command := do
  let mut defs := #[]
  for i in *...ctx.typeInfos.size do
    let indVal := ctx.typeInfos[i]!
    let header ← mkHeaderWithField ``FromValue ``FromField 0 indVal
    let v := mkIdent (← mkFreshUserName `value)
    let binders := header.binders.push (← `(bracketedBinderF|($v : ExactJSON.Value)))
    let auxFun := mkIdent ctx.auxFunNames[i]!
    let recursive := ctx.usePartial || indVal.isRec
    let fueled := recursive && ctx.typeInfos.size == 1 && indVal.numIndices == 0
    let decode := mkIdent (← mkFreshUserName `decode)
    let recur := if fueled then decode else mkIdent ctx.auxFunNames[0]!
    let body ← Term.elabBinders binders fun _ => do
      let type ← Term.elabTerm header.targetType none
      let indName := type.getAppFn.constName!
      if isStructure (← getEnv) indName then mkFromValueStruct indName v
      else mkFromValueInduct recur indName v
    let resultType ← mkInductiveApp indVal header.argNames
    if fueled then
      let inst := mkIdent (← mkFreshUserName `localinst)
      defs := defs.push (← `(def $auxFun:ident $binders:bracketedBinder* : Except String $resultType :=
        ExactJSON.Derive.fix (fun $decode:ident $v:ident =>
          let $inst:ident : ExactJSON.FromValue $resultType := ⟨$decode⟩; $body) $v))
    else if recursive then
      let letDecls ← mkLocalInstanceLetDecls ctx ``FromValue header.argNames
      let body ← mkLet letDecls body
      defs := defs.push (← `(partial def $auxFun:ident $binders:bracketedBinder* : Except String $resultType := $body:term))
    else
      defs := defs.push (← `(def $auxFun:ident $binders:bracketedBinder* : Except String $resultType := $body:term))
  `(mutual $defs:command* end)

def mkNotNullInstance (declName : Name) : TermElabM Command := do
  let indVal ← getConstInfoInduct declName
  let argNames ← mkInductArgNames indVal
  let binders ← mkImplicitBinders argNames
  let indType ← mkInductiveApp indVal argNames
  `(instance $binders:implicitBinder* : ExactJSON.NotNull $indType := ⟨⟩)

def mkToValueHandler (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty || !(← declNames.allM isInductive) then return false
  for declName in declNames do
    let cmds ← liftTermElabM do
      let ctx ← mkContext ``ToValue "toValue" declName
      return #[← mkToValueFuns ctx] ++ (← mkInstanceWithField ctx ``ToValue ``ToField declName) ++
        #[← mkNotNullInstance declName]
    cmds.forM elabCommand
  return true

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

end ExactJSON.Derive

end
