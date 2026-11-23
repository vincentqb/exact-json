module

public import TomlJson.Value
public import TomlJson.Float

/-! # Writing canonical text

`Value.render` writes a value as one line of JSON: no whitespace, members in the order given,
integers without a point, floats with the shortest digits that read back and always a point, and
strings with JSON's minimal escaping. It changes nothing: a valid value gets its canonical text,
an invalid one (see `Value.isValid`) a text that `Value.parse` rejects.
-/

public section

namespace TomlJson

/-- The lowercase hexadecimal digit of `n < 16`. -/
private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `out` followed by `c` as a JSON string holds it: `"` and `\` escaped; U+0008, U+0009, U+000A,
U+000C, U+000D as `\b`, `\t`, `\n`, `\f`, `\r`; the other characters below U+0020 as `\u00xx`
(lowercase); every other character as itself. -/
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

/-- `out` followed by `s` as a JSON string. -/
def pushString (out s : String) : String :=
  (s.foldl pushChar (out.push '"')).push '"'

/-- The text of a float: the canonical text of a finite one (`Float.toCanonical?`); for a NaN or
an infinity, which JSON cannot write, the bare token `NaN`, `Infinity` or `-Infinity`, which no
JSON reader (this one included) accepts. -/
def floatText (x : Float) : String :=
  match Float.toCanonical? x with
  | some text => text
  | none => if x.isNaN then "NaN" else if x > 0 then "Infinity" else "-Infinity"

namespace Value

/-- `out` followed by the text of `v`. -/
partial def renderTo (out : String) : Value → String
  | .null => out ++ "null"
  | .string s => pushString out s
  | .integer n => out ++ toString n
  | .float x => out ++ floatText x
  | .boolean b => out ++ if b then "true" else "false"
  | .array items =>
    let (out, _) := items.foldl (init := (out.push '[', true)) fun (out, first) item =>
      (renderTo (if first then out else out.push ',') item, false)
    out.push ']'
  | .table members =>
    let (out, _) := members.foldl (init := (out.push '{', true)) fun (out, first) (key, item) =>
      (renderTo (pushString (if first then out else out.push ',') key |>.push ':') item, false)
    out.push '}'

/-- The text of `v`: one line of JSON, without its line feed; canonical when `v` is valid. -/
def render (v : Value) : String := renderTo "" v

/-- The JSON Lines text of some values: each one's text and a line feed. -/
def renderLines (vs : Array Value) : String :=
  vs.foldl (fun out v => (renderTo out v).push '\n') ""

instance : ToString Value := ⟨render⟩

end Value

end TomlJson
