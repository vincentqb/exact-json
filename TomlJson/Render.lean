module

public import TomlJson.Value
public import TomlJson.Float

/-! # Writing canonical text

`Value.render` writes a value's normal form as one line of canonical JSON (see `SPEC.md`):
no whitespace, tables sorted by key, integers without a point, floats always with one, and
strings escaped so that the line holds no control character and no line separator.
-/

public section

namespace TomlJson

/-- The lowercase hexadecimal digit of `n < 16`. -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Whether a string holds `c` as an escape rather than as itself: `"`, `\`, the control
characters (Unicode category Cc: U+0000–U+001F, U+007F–U+009F) and the line and paragraph
separators U+2028, U+2029. -/
def mustEscape (c : Char) : Bool :=
  c == '"' || c == '\\' || c.val < 0x20 || (0x7F ≤ c.val && c.val ≤ 0x9F) ||
    c.val == 0x2028 || c.val == 0x2029

/-- `out` followed by the canonical escape of `c`: the two-character escape where JSON has one,
`\u` and four lowercase hexadecimal digits otherwise; `c` itself when it needs no escape. -/
def pushChar (out : String) (c : Char) : String :=
  if !mustEscape c then out.push c
  else if c == '"' then out ++ "\\\""
  else if c == '\\' then out ++ "\\\\"
  else if c == '\x08' then out ++ "\\b"
  else if c == '\t' then out ++ "\\t"
  else if c == '\n' then out ++ "\\n"
  else if c == '\x0c' then out ++ "\\f"
  else if c == '\r' then out ++ "\\r"
  else
    let n := c.toNat
    (((out ++ "\\u").push (hexDigit (n / 4096 % 16))).push (hexDigit (n / 256 % 16))
      |>.push (hexDigit (n / 16 % 16))).push (hexDigit (n % 16))

/-- `out` followed by `s` as a canonical JSON string. -/
def pushString (out s : String) : String :=
  (s.foldl pushChar (out.push '"')).push '"'

/-- The canonical text of a float: `Float.toCanonical?` for a finite one, its name as a string
(`"NaN"`, `"Infinity"`, `"-Infinity"`) for the others. -/
def floatText (x : Float) : String :=
  match Float.toCanonical? x with
  | some text => text
  | none => pushString "" (Value.nonFiniteName x)

namespace Value

/-- `out` followed by the canonical text of `v`'s normal form. -/
partial def renderTo (out : String) : Value → String
  | .string s => pushString out s
  | .integer n => out ++ toString n
  | .float x => out ++ floatText x
  | .boolean b => out ++ if b then "true" else "false"
  | .array items =>
    let (out, _) := items.foldl (init := (out.push '[', true)) fun (out, first) item =>
      (renderTo (if first then out else out.push ',') item, false)
    out.push ']'
  | .table members =>
    let (out, _) := (sortMembers members).foldl (init := (out.push '{', true))
      fun (out, first) (key, item) =>
        (renderTo (pushString (if first then out else out.push ',') key |>.push ':') item, false)
    out.push '}'

/-- The canonical text of `v`: one line of JSON, without its line feed. It is the text of
`v.normalize`, so values with the same normal form have the same text. -/
def render (v : Value) : String := renderTo "" v

/-- The canonical JSON Lines text of some values: each one's text and a line feed. -/
def renderLines (vs : Array Value) : String :=
  vs.foldl (fun out v => (renderTo out v).push '\n') ""

instance : ToString Value := ⟨render⟩

end Value

end TomlJson
