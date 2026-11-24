module

import ExactJSON
meta import ExactJSON

/-! Examples of the format, checked when this module is built (`lake test`). -/

open ExactJSON

/-- `ok` if `s` is canonical (and reads back to itself), else the reader's error. -/
def check (s : String) : String :=
  match Value.parse s with
  | .ok v => if v.render == s then "ok" else s!"read, but written back as {v.render}"
  | .error e => e

/-- Whether `e` succeeded with `x`. -/
def gives {α : Type} [BEq α] (e : Except String α) (x : α) : Bool :=
  match e with
  | .ok y => y == x
  | .error _ => false

/-- The error of `e`, or `"ok"`. -/
def errorOf {α : Type} (e : Except String α) : String :=
  match e with
  | .ok _ => "ok"
  | .error e => e

/-! ## Canonical text is read; anything else is an error naming the canonical spelling -/

#guard ["null", "true", "false", "0", "-17", "123456789012345678901234567890", "1.0", "-0.0", "0.1",
  "1.5e-7", "1.0e16", "5.0e-324", "1.7976931348623157e308", "\"\"", "\"a\\tb\"", "[]", "{}",
  "[1,2.5,\"x\",null,[],{}]", "{\"a\":{\"b\":[null]},\"b\":1}"].all (check · == "ok")
-- integers have no point, floats always one, with the shortest digits that read back
#guard check "1e5" == "at character 0: not the canonical text of this float: write 100000.0"
#guard check "1.50" == "at character 0: not the canonical text of this float: write 1.5"
#guard check "1.0e+16" == "at character 0: not the canonical text of this float: write 1.0e16"
#guard check "0.00001" == "at character 0: not the canonical text of this float: write 1.0e-5"
#guard check "1e16" == "at character 0: not the canonical text of this float: write 1.0e16"
#guard check "0.1000000000000000055511151231257827" ==
  "at character 0: not the canonical text of this float: write 0.1"
#guard check "9007199254740993.0" == "at character 0: not the canonical text of this float: write 9007199254740992.0"
#guard check "-0" == "at character 0: not the canonical text of this integer: write 0"
#guard check "01" == "at character 0: not the canonical text of this integer: write 1"
#guard check "-01" == "at character 0: not the canonical text of this integer: write -1"
#guard check "00.5" == "at character 0: not the canonical text of this float: write 0.5"
#guard check "1e400" == "at character 0: a float beyond the range of binary64"
-- an exponent's leading zeros, however many, do not change the float it denotes
#guard check ("1e" ++ String.ofList (List.replicate 5000 '0') ++ "1") ==
  "at character 0: not the canonical text of this float: write 10.0"
-- a long exponent costs no arithmetic: past the text's length, the float is infinite or zero
#guard check ("1e" ++ String.ofList (List.replicate 100000 '9')) ==
  "at character 0: a float beyond the range of binary64"
#guard check ("1e-" ++ String.ofList (List.replicate 100000 '9')) ==
  "at character 0: not the canonical text of this float: write 0.0"
#guard check ("0.0e" ++ String.ofList (List.replicate 100000 '9')) ==
  "at character 0: not the canonical text of this float: write 0.0"
-- no whitespace anywhere
#guard check " 1" == "at character 0: canonical text has no whitespace"
#guard check "[1, 2]" == "at character 3: canonical text has no whitespace"
#guard check "{\"a\": 1}" == "at character 5: canonical text has no whitespace"
#guard check "1\n" == "at character 1: text after the value (canonical text has no whitespace)"

/-! ## Strings: JSON's minimal escaping -/

#guard Value.render (.string "tab\t nl\n cr\r bs\x08 ff\x0c q\" bsl\\ nul\x00 us\x1f") ==
  "\"tab\\t nl\\n cr\\r bs\\b ff\\f q\\\" bsl\\\\ nul\\u0000 us\\u001f\""
-- DEL, C1 controls, U+2028 and everything else as themselves
#guard Value.render (.string "\x7f\u0085\u2028/é😀") == "\"\x7f\u0085\u2028/é😀\""
#guard check "\"\\/\"" == "at character 1: write /, not \\/"
#guard check "\"\\u0041\"" == "at character 1: write A, not \\u0041"
#guard check "\"\\u0100\"" == "at character 1: write Ā, not \\u0100"
#guard check "\"\\u000a\"" == "at character 1: write \\n, not \\u000a"
#guard check "\"\\u0022\"" == "at character 1: write \\\", not \\u0022"
#guard check "\"\\u001F\"" == "at character 1: write \\u001f, not \\u001F"
#guard check "\"\\ud83d\\ude00\"" == "at character 1: write 😀, not the surrogate pair \\ud83d\\ude00"
#guard check "\"\\udc00\"" == "at character 1: \\udc00 is a lone surrogate, not a character"
#guard check "\"a\tb\"" == "at character 2: control character in string (it must be escaped)"

/-! ## Arrays and tables -/

-- keys in code point order (U+FFFF before U+10000: not UTF-16 order)
#guard check ("{\"B\":1,\"a\":2,\"" ++ String.singleton (Char.ofNat 0xFFFF) ++ "\":3,\"" ++
  String.singleton (Char.ofNat 0x10000) ++ "\":4}") == "ok"
#guard check "{\"b\":1,\"a\":2}" == "at character 7: keys must increase: \"a\" comes before \"b\""
#guard check "{\"a\":1,\"a\":2}" == "at character 7: duplicate key \"a\""
#guard check "{\"a\":null}" == "ok"

/-! ## Not JSON -/

#guard ["", "{", "[1,]", "[,1]", "{\"a\":1,}", "1.", ".5", "-", "1e", "+1", "tru", "nul",
  "[1 2]", "{}x", "'a'", "{1:2}", "NaN", "Infinity", "\"\\x\"", "0x10", "1_000"].all
  fun s => !(Value.parse s).isOk

/-! ## Invalid values are written as text that is not read back as another value -/

#guard (Value.table #[("b", 1), ("a", 2)]).render == "{\"b\":1,\"a\":2}"
#guard !(Value.table #[("b", 1), ("a", 2)]).isValid
#guard (Value.float (0.0 / 0.0)).render == "NaN"
#guard !(Value.parse (Value.array #[.float (1.0 / 0.0)]).render).isOk

/-! ## Nesting -/

-- the reader's fuel outlasts any text: a text cut short is an error at its end
#guard check "[[[[" == "at character 4: expected a value, found the end of the text"
#guard check "{\"a\":[{\"b\":" == "at character 11: expected a value, found the end of the text"
#guard check (String.ofList (List.replicate 2000 '[' ++ List.replicate 2000 ']')) == "ok"
#guard check (String.ofList (List.replicate 2000 '[')) ==
  "at character 2000: expected a value, found the end of the text"

/-! ## Reading any JSON (RFC 8259) -/

/-- The canonical text of what the JSON text `s` holds, or why it is not read. -/
def canon (s : String) : String :=
  match Value.readJson s with
  | .ok v => v.render
  | .error e => e

-- any spelling: whitespace, escapes, number spellings, members in any order
#guard canon " {\"b\" : [1, 2.50, -0, 1E+2, 1e-2, 0.5e1], \"a\":\t\"\\u00e9\\/\\ud83d\\ude00\\n\"}\r\n" ==
  "{\"a\":\"é/😀\\n\",\"b\":[1,2.5,0,100.0,0.01,5.0]}"
#guard canon "[ ]" == "[]"
#guard canon "{ }" == "{}"
-- a canonical text is read as itself
#guard ["null", "true", "-17", "1.0e16", "[1,2.5,\"x\",{}]", "{\"a\":{\"b\":[null]},\"b\":1}"].all
  fun s => canon s == s
-- not JSON: trailing commas, comments, leading zeros, bare tokens, single quotes, raw control
-- characters, bad escapes, a byte order mark, missing separators, unclosed or trailing text
#guard ["", " ", "[1,]", "{\"a\":1,}", "01", "-01", "-", "1.", ".5", "+1", "1e", "NaN", "Infinity", "'a'",
  "[1 2]", "{\"a\" 1}", "{a:1}", "\"\t\"", "\"\\x\"", "\"\\u12\"", "// c\n1", "\ufeff1", "tru", "1 2",
  "[", "{\"a\":1", "\"a", "0x10"].all fun s => !(Value.readJson s).isOk
-- what a value cannot hold is not read
#guard canon "{\"a\":1,\"a\":2}" == "at character 7: a key repeats"
#guard canon "\"\\udc00\"" == "at character 1: a low surrogate not after a high one"
#guard canon "\"\\ud800x\"" == "at character 1: a high surrogate not followed by a low one"
#guard canon "1e400" == "at character 0: a float beyond the range of binary64"
#guard canon "[1,]" == "at character 3: expected a value"

/-! ## JSON Lines -/

#guard gives ((Value.parseLines "{\"a\":1}\n[2]\n").map (·.map Value.render)) #["{\"a\":1}", "[2]"]
#guard gives ((Value.parseLines "").map (·.size)) 0
#guard errorOf (Value.parseLines "{\"a\":1}\n[2]") == "line 2: no line feed at its end"
-- the first line that is not canonical is the one reported
#guard errorOf (Value.parseLines "1\n[\n3") == "line 2, at character 1: expected a value, found the end of the text"
#guard errorOf (Value.parseLines "1\n\n2\n") == "line 2, at character 0: expected a value, found the end of the text"
#guard errorOf (Value.parseLines "1\r\n") == "line 1, at character 1: text after the value (canonical text has no whitespace)"

/-! ## The `exactjson%` literal -/

#guard (exactjson% {"b": 1, "a": 1.0, c: [-2, -0.5, "x", true, null], "d": {}}).render ==
  "{\"a\":1.0,\"b\":1,\"c\":[-2,-0.5,\"x\",true,null],\"d\":{}}"
#guard (exactjson% {"n": $(3 + 4), "s": $("a" ++ "b")}).render == "{\"n\":7,\"s\":\"ab\"}"
#guard (exactjson% {«a b»: 1, «1»: 2}).render == "{\"1\":2,\"a b\":1}"
/-- `exactjson%` inside a macro: hygiene must not reach the keys. -/
macro "keysInMacro" : term => `(exactjson% {foo: 1, "bar": 2})
#guard (keysInMacro).render == "{\"bar\":2,\"foo\":1}"

/-! ## Typed values -/

/-- An example record. -/
structure Run where
  /-- Its name. -/
  name : String
  /-- Iterations. -/
  iters : Nat
  /-- Seconds, when measured. -/
  time? : Option Float
  /-- When. -/
  day : LocalDate
  deriving ToValue, FromValue

/-- A record. -/
def run : Run := { name := "a", iters := 3, time? := some 2.0, day := ⟨2024, 2, 29⟩ }

#guard encode run == "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"time\":2.0}"
-- a `none` field is an absent key
#guard encode { run with time? := none } == "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\"}"
#guard gives ((decode (encode run) : Except String Run).map encode) (encode run)
#guard gives ((decode (encode { run with time? := none }) : Except String Run).map encode)
  (encode { run with time? := none })
-- strict: an integer for a float, an unknown key, `null` for a `none` field, a missing key
#guard errorOf (decode "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"time\":2}" : Except String Run) ==
  "time: expected a float, found integer 2"
#guard errorOf (decode "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"x\":0}" : Except String Run) ==
  "Run has no field \"x\""
#guard errorOf (decode "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"time\":null}" : Except String Run) ==
  "time: expected a float, found null null"
#guard errorOf (decode "{\"day\":\"2024-02-29\",\"name\":\"a\"}" : Except String Run) == "missing key \"iters\""
#guard errorOf (decode "{\"day\":\"2023-02-29\",\"iters\":1,\"name\":\"a\"}" : Except String Run) ==
  "day: expected a date-time, date or time in canonical RFC 3339 form, found string \"2023-02-29\""

/-! ## `none`: an absent key as a field, `null` elsewhere -/

#guard encode #[some 1, none, some 3] == "[1,null,3]"
#guard gives (decode "[1,null,3]" : Except String (Array (Option Nat))) #[some 1, none, some 3]

/-- A field that is optional twice over: absent, `null` or a value. -/
structure Twice where
  /-- The field. -/
  x : Option (Option Nat)
  deriving ToValue, FromValue

#guard [({ x := none } : Twice), { x := some none }, { x := some (some 2) }].map encode ==
  ["{}", "{\"x\":null}", "{\"x\":2}"]
#guard ["{}", "{\"x\":null}", "{\"x\":2}"].all fun s =>
  gives ((decode s : Except String Twice).map encode) s

/-- A field whose type is a parameter: instantiated to an `Option`, it is a key that may be
absent, like any `Option` field. -/
structure Box (α : Type) where
  /-- The field. -/
  x : α
  deriving ToValue, FromValue

/-- A constructor argument whose type is a parameter. -/
inductive Leaf (α : Type) where
  /-- The leaf. -/
  | leaf (x : α)
  deriving ToValue, FromValue

#guard encode ({ x := none } : Box (Option Nat)) == "{}"
#guard encode ({ x := some 1 } : Box (Option Nat)) == "{\"x\":1}"
#guard (decode "{}" : Except String (Box (Option Nat))).isOk
#guard encode (Leaf.leaf (none : Option Nat)) == "{\"leaf\":{}}"
#guard encode ({ x := 3 } : Box Nat) == "{\"x\":3}"

/-! ## Sum types -/

/-- An example sum type. -/
inductive Shape where
  /-- A circle. -/
  | circle (radius : Float)
  /-- A rectangle. -/
  | rect (w h : Float)
  /-- A pair of anything. -/
  | pair : Nat → String → Shape
  /-- A point. -/
  | dot
  deriving ToValue, FromValue

#guard [Shape.circle 1, .rect 2 0.5, .pair 7 "s", .dot].map encode ==
  ["{\"circle\":{\"radius\":1.0}}", "{\"rect\":{\"h\":0.5,\"w\":2.0}}", "{\"pair\":[7,\"s\"]}", "\"dot\""]
#guard errorOf (decode "{\"rect\":{\"w\":1.0}}" : Except String Shape) == "rect: missing key \"h\""
#guard errorOf (decode "{\"circle\":{\"r\":1.0,\"radius\":1.0}}" : Except String Shape) ==
  "circle: circle has no field \"r\""
#guard errorOf (decode "\"square\"" : Except String Shape) == "unknown constructor \"square\""

/-- A constructor whose named arguments are all optional. -/
inductive Cmd where
  /-- Run. -/
  | run (verbose? : Option Bool) (level? : Option Nat)
  /-- Stop. -/
  | stop
  deriving ToValue, FromValue

-- its payload must still be a table
#guard ["{\"run\":5}", "{\"run\":\"x\"}", "{\"run\":[true]}"].all fun s => !(decode s : Except String Cmd).isOk
#guard (decode "{\"run\":{}}" : Except String Cmd).isOk

/-! ## Floats and integers -/

-- floats that are not finite are strings, read back as floats
#guard encode #[1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, -0.0] == "[\"Infinity\",\"-Infinity\",\"NaN\",-0.0]"
#guard gives ((decode "[\"Infinity\",-0.0]" : Except String (Array Float)).map fun xs => xs.map (·.toBits))
  #[(1.0 / 0.0 : Float).toBits, (-0.0 : Float).toBits]
-- fixed-width integers check their range
#guard !(decode "256" : Except String UInt8).isOk
#guard gives ((decode "-128" : Except String Int8).map (·.toInt)) (-128)

/-! ## Date-times: one canonical RFC 3339 form each -/

#guard ["1979-05-27T07:32:00Z", "1979-05-27T00:32:00.999999-07:00", "1979-05-27T07:32:00.5",
  "1979-05-27", "07:32:00", "23:59:60", "00:00:00.000000001"].all fun s =>
  (DateTime.parse? s).map toString == some s
-- other spellings TOML or ISO 8601 allow are not read
#guard ["1979-05-27t07:32:00Z", "1979-05-27 07:32:00Z", "1979-05-27T07:32:00z",
  "1979-05-27T07:32:00+00:00", "1979-05-27T07:32", "07:32:00.50", "07:32:00.5000000001",
  "2024-13-01", "2023-02-29", "24:00:00", "1979-05-27T07:32:00+24:00", "1979-5-27"].all
  fun s => (DateTime.parse? s).isNone
#guard (OffsetDateTime.ofUnixNanos? 0).map toString == some "1970-01-01T00:00:00Z"
#guard (OffsetDateTime.ofUnixNanos? 951782400123456789).map toString == some "2000-02-29T00:00:00.123456789Z"
#guard (OffsetDateTime.ofUnixNanos? (-1)).map toString == some "1969-12-31T23:59:59.999999999Z"
-- the representable instants: years 0 to 9999
#guard (OffsetDateTime.ofUnixNanos? (-62167219200 * 1000000000)).map toString == some "0000-01-01T00:00:00Z"
#guard (OffsetDateTime.ofUnixNanos? (-62167219200 * 1000000000 - 1)).isNone
#guard (OffsetDateTime.ofUnixNanos? (253402300800 * 1000000000 - 1)).map toString ==
  some "9999-12-31T23:59:59.999999999Z"
#guard (OffsetDateTime.ofUnixNanos? (253402300800 * 1000000000)).isNone
#guard (DateTime.parse? "2000-02-29T05:30:00+05:30").all fun
  | .offsetDateTime dt => dt.toUnixNanos == 951782400 * 1000000000
  | _ => false
-- an invalid time is not written as some other, valid, time
#guard !(decode (encode ({ hour := 0, minute := 0, second := 0, nanosecond := 1000000000 } : LocalTime))
  : Except String LocalTime).isOk

/-! ## `Lean.Json` -/

#guard gives ((Value.parse "{\"a\":[1,1.0,0.5,1.0e16,\"s\",null]}").map (·.toJson.compress))
  "{\"a\":[1,1,0.5,10000000000000000,\"s\",null]}"
#guard gives (((Value.parse "{\"a\":[1,1.0,1.0e16,null]}").toOption.get!.toJson |> Value.ofJson?).map Value.render)
  "{\"a\":[1,1.0,1.0e16,null]}"
-- Lean's `ToJson Float` loses digits; `floatToJson` does not
#guard (Lean.toJson (1e-7 : Float)).compress == "0"
#guard (floatToJson 1e-7).compress == "0.0000001"
#guard (floatToJson 0.1234567).compress == "0.1234567"

-- `open scoped ExactJSON.ExactFloat` makes Lean's own `ToJson` exact, derived instances included
section
open scoped ExactJSON.ExactFloat

/-- A record with Lean's own JSON instances. -/
structure Timing where
  /-- Seconds. -/
  seconds : Float
  deriving Lean.ToJson

#guard (Lean.toJson (1e-7 : Float)).compress == "0.0000001"
#guard (Lean.toJson ({ seconds := 0.1234567 } : Timing)).compress == "{\"seconds\":0.1234567}"
end

/-! ## The README's examples -/

/-- The README's record. -/
structure Bench where
  /-- Its name. -/
  name : String
  /-- Iterations. -/
  iters : Nat
  /-- Seconds, when measured: an optional key. -/
  time? : Option Float
  /-- The day it ran: a string `YYYY-MM-DD`. -/
  day : LocalDate
  deriving ToValue, FromValue, Repr

/-- info: {"day":"2024-02-29","iters":100,"name":"fast","time":2.0} -/
#guard_msgs in
#eval IO.println (encode ({ name := "fast", iters := 100, time? := some 2.0, day := ⟨2024, 2, 29⟩ } : Bench))

/-- info: Except.error "missing key \"day\"" -/
#guard_msgs in
#eval (decode "{\"iters\":100,\"name\":\"fast\"}" : Except String Bench)
#guard (exactjson% {"name": "fast", "iters": 100, "time": 2.0, "sizes": [1, 2],
  "day": $(LocalDate.mk 2024 2 29)}).render ==
  "{\"day\":\"2024-02-29\",\"iters\":100,\"name\":\"fast\",\"sizes\":[1,2],\"time\":2.0}"
#guard (decode "{\"day\":\"2024-02-29\",\"iters\":100,\"name\":\"fast\"}" : Except String Bench).isOk
#guard errorOf (decode "{\"iters\":100,\"name\":\"fast\"}" : Except String Bench) == "missing key \"day\""
