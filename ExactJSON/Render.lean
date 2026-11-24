module

public import ExactJSON.Value
public import ExactJSON.Float

@[expose] public section

namespace ExactJSON

def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

def pushChar (out : String) (c : Char) : String :=
  if c == '"' then out ++ "\\\""
  else if c == '\\' then out ++ "\\\\"
  else if c.val ≥ 0x20 then out.push c
  else if c == '\x08' then out ++ "\\b"
  else if c == '\t' then out ++ "\\t"
  else if c == '\n' then out ++ "\\n"
  else if c == '\x0c' then out ++ "\\f"
  else if c == '\r' then out ++ "\\r"
  else ((out ++ "\\u00").push (hexDigit (c.toNat / 16))).push (hexDigit (c.toNat % 16))

def pushString (out s : String) : String :=
  (s.foldl pushChar (out.push '"')).push '"'

def floatText (x : Float) : String :=
  match Float.toCanonical? x with
  | some text => text
  | none => if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity"

namespace Value

mutual

def renderTo (out : String) : Value → String
  | .null => out ++ "null"
  | .string s => pushString out s
  | .integer n => out ++ toString n
  | .float x => out ++ floatText x
  | .boolean b => out ++ if b then "true" else "false"
  | .array ⟨items⟩ => (renderItems (out.push '[') items).push ']'
  | .table ⟨members⟩ => (renderMembers (out.push '{') members).push '}'

def renderItems (out : String) : List Value → String
  | [] => out
  | [v] => renderTo out v
  | v :: rest => renderItems ((renderTo out v).push ',') rest

def renderMembers (out : String) : List (String × Value) → String
  | [] => out
  | [(k, v)] => renderTo ((pushString out k).push ':') v
  | (k, v) :: rest => renderMembers ((renderTo ((pushString out k).push ':') v).push ',') rest

end

def render (v : Value) : String := renderTo "" v

def renderLines (vs : Array Value) : String :=
  vs.foldl (fun out v => (renderTo out v).push '\n') ""


end Value

end ExactJSON
