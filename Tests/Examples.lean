module

import TomlJson
meta import TomlJson

/-! Examples of the format, checked when this module is built (`lake test`). The examples in
`SPEC.md` and `README.md` are among them. -/

open TomlJson

/-- The canonical text of the value a JSON text denotes, or the error. -/
def canon (s : String) : String :=
  match Value.parse s with
  | .ok v => v.render
  | .error e => "error: " ++ e

/-- Whether `s` is canonical. -/
def isCanonical (s : String) : Bool := (Value.parseCanonical s).isOk

/-- Whether `e` succeeded with `x`. -/
def gives {α : Type} [BEq α] (e : Except String α) (x : α) : Bool :=
  match e with
  | .ok y => y == x
  | .error _ => false

/-! ## Scalars -/

-- integers have no point, floats always one
#guard canon "1" == "1"
#guard canon "1.0" == "1.0"
#guard canon "1.50" == "1.5"
#guard canon "1e5" == "100000.0"
#guard canon "1E+5" == "100000.0"
#guard canon "-0" == "0"
#guard canon "-0.0" == "-0.0"
#guard canon "123456789012345678901234567890" == "123456789012345678901234567890"
#guard canon "-9223372036854775808" == "-9223372036854775808"
-- the shortest digits that read back, in Python's layout (fixed in [1e-4, 1e16))
#guard canon "0.1" == "0.1"
#guard canon "0.30000000000000004" == "0.30000000000000004"
#guard canon "0.1000000000000000055511151231257827" == "0.1"
#guard canon "0.0001" == "0.0001"
#guard canon "0.00001" == "1.0e-5"
#guard canon "1e15" == "1000000000000000.0"
#guard canon "1e16" == "1.0e16"
#guard canon "1.7976931348623157e308" == "1.7976931348623157e308"
#guard canon "5e-324" == "5.0e-324"
#guard canon "2e-324" == "0.0"
#guard canon "1e400" == "error: at byte 0: a float beyond the range of binary64"
#guard canon "1e-999999999999" == "0.0"
#guard canon "9007199254740993.0" == "9007199254740992.0"
-- booleans
#guard canon " true " == "true"
#guard canon "false" == "false"

/-! ## Strings -/

-- `\uXXXX` escapes only where needed; two-character escapes where JSON has them
#guard canon "\"\\u0041\\/\\u00e9\"" == "\"A/é\""
#guard canon "\"\\ud83d\\ude00\"" == "\"😀\""
#guard Value.render (.string "tab\t nl\n cr\r bs\x08 ff\x0c q\" bsl\\") ==
  "\"tab\\t nl\\n cr\\r bs\\b ff\\f q\\\" bsl\\\\\""
-- every control character (C0, DEL, C1) and U+2028, U+2029 escaped: no line breaks in a line
#guard Value.render (.string "\x00\x1f\x7f\u0085\u2028\u2029") ==
  "\"\\u0000\\u001f\\u007f\\u0085\\u2028\\u2029\""
#guard (Value.render (.string (String.ofList ((List.range 0x2100).map Char.ofNat)))).all
  fun c => c.val ≥ 0x20 && !(0x7F ≤ c.val && c.val ≤ 0x9F) && c.val != 0x2028 && c.val != 0x2029
#guard canon "\"\\ud800\"" == "error: at byte 1: unpaired surrogate (a Lean string holds only scalar values)"
#guard canon "\"a\tb\"" == "error: at byte 2: control character in string (it must be escaped)"

/-! ## Arrays and tables -/

#guard canon " [ 1 , 2.5 , \"x\" , [ ] , { } ] " == "[1,2.5,\"x\",[],{}]"
-- keys sorted by code point (U+FFFF before U+10000: not UTF-16 order)
#guard canon "{\"b\":1,\"a\":2,\"B\":3,\"\\ud800\\udc00\":4,\"\\uffff\":5}" ==
  "{\"B\":3,\"a\":2,\"b\":1,\"" ++ String.singleton (Char.ofNat 0xFFFF) ++ "\":5,\"" ++
    String.singleton (Char.ofNat 0x10000) ++ "\":4}"
-- a null member is an absent key; null anywhere else has no meaning
#guard canon "{\"a\":null,\"b\":1}" == "{\"b\":1}"
#guard canon "[1,null]" == "error: at byte 3: null has no TOML counterpart (only a table member may be null: it is dropped)"
#guard canon "null" == "error: at byte 0: null has no TOML counterpart"
#guard canon "{\"a\":1,\"a\":1}" == "error: at byte 7: duplicate key \"a\""
-- the first repeat in the text is the one reported
#guard canon "{\"b\":1,\"a\":1,\"a\":2,\"b\":2,\"a\":3}" == "error: at byte 13: duplicate key \"a\""

/-! ## Malformed JSON -/

#guard ["", " ", "{", "[1,]", "[,1]", "{\"a\" 1}", "{\"a\":1,}", "01", "1.", ".5", "-", "1e", "+1",
  "tru", "nul", "[1 2]", "{} x", "1 2", "'a'", "{1:2}", "NaN", "Infinity", "\"\\x\"", "\"\\u12g4\"",
  "0x10", "1_000"].all fun s => !(Value.parse s).isOk

/-! ## Canonical text -/

#guard isCanonical "{\"a\":[1,2.0,\"x\"],\"b\":{\"c\":true}}"
#guard ["{\"b\":1,\"a\":2}", "{\"a\": 1}", " 1", "1.00", "1e5", "1.0e+16", "1.0E16", "-0",
  "\"\\u0041\"", "\"\\/\"", "\"\u2028\"", "{\"a\":null}", "1.0e-05", "100000000000000000.0"].all
  (!isCanonical ·)
#guard match Value.parseCanonical "{\"b\":1,\"a\":2}" with
  | .error e => e == "at byte 2: not canonical: the canonical text continues `a\":2,\"b\":1}`, this one `b\":1,\"a\":2}`"
  | .ok _ => false

/-! ## Normal form -/

-- later members win; non-finite floats are written as their names
#guard (Value.mkTable [("z", .float (0.0 / 0.0)), ("a", .float (1.0 / 0.0)), ("a", 3)]).render ==
  "{\"a\":3,\"z\":\"NaN\"}"
#guard (Value.table #[("b", 1), ("a", 2)]).render == "{\"a\":2,\"b\":1}"
#guard !(Value.table #[("b", 1), ("a", 2)]).isNormal
#guard (Value.float (-1.0 / 0.0)).render == "\"-Infinity\""

/-! ## JSON Lines -/

#guard gives ((Value.parseLines "{\"a\":1}\r\n\n  \n[2]").map (·.map Value.render)) (#["{\"a\":1}", "[2]"])
-- a blank line is one of JSON whitespace only
#guard gives ((Value.parseLines " \r \n\r\r\n\t\n1\n").map (·.map Value.render)) #["1"]
#guard (Value.parseLinesCanonical "{\"a\":1}\n[2]\n").isOk
#guard !(Value.parseLinesCanonical "{\"a\":1}\n[2]").isOk
#guard !(Value.parseLinesCanonical "{\"a\":1}\n\n[2]\n").isOk
#guard !(Value.parseLinesCanonical "{\"a\":1}\r\n").isOk

/-! ## The `tomljson%` literal -/

#guard (tomljson% {"b": 1, "a": 1.0, c: [-2, -0.5, "x", true], "d": {}}).render ==
  "{\"a\":1.0,\"b\":1,\"c\":[-2,-0.5,\"x\",true],\"d\":{}}"
#guard (tomljson% {"n": $(3 + 4), "s": $("a" ++ "b")}).render == "{\"n\":7,\"s\":\"ab\"}"

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
#guard encode { run with time? := none } == "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\"}"
#guard gives ((decodeCanonical (encode run) : Except String Run).map encode) ((encode run))
-- lenient decoding: an integer for a float, an unknown key, a missing optional key
#guard gives ((decode "{\"name\":\"a\",\"iters\":3,\"time\":2,\"day\":\"2024-02-29\",\"x\":0}" : Except String Run).map encode) ((encode run))
-- canonical decoding takes none of those
#guard !(decodeCanonical "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"time\":2}" : Except String Run).isOk
#guard !(decodeCanonical "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"x\":0}" : Except String Run).isOk
#guard match (decode "{\"name\":\"a\",\"iters\":-1,\"day\":\"2024-02-29\"}" : Except String Run) with
  | .error e => e == "iters: expected a natural number, found integer -1"
  | .ok _ => false
#guard match (decode "{\"name\":\"a\",\"iters\":1,\"day\":\"2023-02-29\"}" : Except String Run) with
  | .error e => e == "day: expected an RFC 3339 date-time, date or time, found string \"2023-02-29\""
  | .ok _ => false

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
#guard match (decode "{\"rect\":{\"w\":1}}" : Except String Shape) with
  | .error e => e == "rect: missing key \"h\""
  | .ok _ => false

-- floats that are not finite are strings, read back as floats
#guard encode #[1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, -0.0] == "[\"Infinity\",\"-Infinity\",\"NaN\",-0.0]"
#guard gives (((decode "[\"Infinity\",-0.0]" : Except String (Array Float)).map fun xs => xs.map (·.toBits))) (#[(1.0 / 0.0 : Float).toBits, (-0.0 : Float).toBits])
#guard !(decode ("1" ++ String.ofList (List.replicate 400 '0')) : Except String Float).isOk
-- fixed-width integers check their range
#guard !(decode "256" : Except String UInt8).isOk
#guard gives ((decode "-128" : Except String Int8).map (·.toInt)) ((-128))

/-! ## Date-times -/

#guard (DateTime.parse? "1979-05-27T07:32:00Z").map toString == some "1979-05-27T07:32:00Z"
#guard (DateTime.parse? "1979-05-27 00:32:00.999999-07:00").map toString == some "1979-05-27T00:32:00.999999-07:00"
#guard (DateTime.parse? "1979-05-27t07:32:00+00:00").map toString == some "1979-05-27T07:32:00Z"
#guard (DateTime.parse? "1979-05-27T07:32").map toString == some "1979-05-27T07:32:00"
#guard (DateTime.parse? "07:32:00.5000000001").map toString == some "07:32:00.5"
#guard (DateTime.parse? "23:59:60").map toString == some "23:59:60"
#guard ["2024-13-01", "2023-02-29", "24:00:00", "1979-05-27T07:32:00+24:00", "1979-5-27",
  "1979-05-27T07:32:00.Z", "1979-05-27X07:32:00"].all fun s => (DateTime.parse? s).isNone
#guard (OffsetDateTime.ofUnixNanos? 0).map toString == some "1970-01-01T00:00:00Z"
#guard (OffsetDateTime.ofUnixNanos? 951782400123456789).map toString == some "2000-02-29T00:00:00.123456789Z"
#guard (OffsetDateTime.ofUnixNanos? (-1)).map toString == some "1969-12-31T23:59:59.999999999Z"
-- the representable instants: years 0 to 9999
#guard (OffsetDateTime.ofUnixNanos? (-62167219200 * 1000000000)).map toString == some "0000-01-01T00:00:00Z"
#guard (OffsetDateTime.ofUnixNanos? (-62167219200 * 1000000000 - 1)).isNone
#guard (OffsetDateTime.ofUnixNanos? (253402300800 * 1000000000 - 1)).map toString ==
  some "9999-12-31T23:59:59.999999999Z"
#guard (OffsetDateTime.ofUnixNanos? (253402300800 * 1000000000)).isNone
-- an invalid time is not written as some other, valid, time
#guard ((decode (encode ({ hour := 0, minute := 0, second := 0, nanosecond := 1000000000 } : LocalTime))
  : Except String LocalTime)).toOption.isNone
#guard (DateTime.parse? "2000-02-29T05:30:00+05:30").all fun
  | .offsetDateTime dt => dt.toUnixNanos == 951782400 * 1000000000
  | _ => false

/-! ## `Lean.Json` -/

#guard gives ((Value.parse "{\"a\":[1,1.0,0.5,1.0e16,\"s\"]}").map (·.toJson.compress)) ("{\"a\":[1,1,0.5,10000000000000000,\"s\"]}")
#guard gives (((Value.parse "{\"a\":[1,1.0,1.0e16]}").toOption.get!.toJson |> Value.ofJson?).map Value.render) ("{\"a\":[1,1.0,1.0e16]}")
#guard gives ((Value.ofJson? (Lean.Json.mkObj [("a", .null), ("b", Lean.toJson [1, 2])])).map Value.render) ("{\"b\":[1,2]}")
-- Lean's `ToJson Float` loses digits; `floatToJson` does not
#guard (Lean.toJson (1e-7 : Float)).compress == "0"
#guard (floatToJson 1e-7).compress == "0.0000001"
#guard (floatToJson 0.1234567).compress == "0.1234567"

-- `open scoped TomlJson.ExactFloat` makes Lean's own `ToJson` exact, derived instances included
section
open scoped TomlJson.ExactFloat

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
  deriving ToValue, FromValue

#guard encode ({ name := "fast", iters := 100, time? := some 2.0, day := ⟨2024, 2, 29⟩ } : Bench) ==
  "{\"day\":\"2024-02-29\",\"iters\":100,\"name\":\"fast\",\"time\":2.0}"
#guard (tomljson% {"name": "fast", "iters": 100, "time": 2.0, "sizes": [1, 2],
  "day": $(LocalDate.mk 2024 2 29)}).render ==
  "{\"day\":\"2024-02-29\",\"iters\":100,\"name\":\"fast\",\"sizes\":[1,2],\"time\":2.0}"
#guard (decodeCanonical "{\"day\":\"2024-02-29\",\"iters\":100,\"name\":\"fast\"}" : Except String Bench).isOk

/-! ## Regressions -/

-- an exponent's leading zeros, however many, do not change it
#guard canon ("1e" ++ String.ofList (List.replicate 5000 '0') ++ "1") == "10.0"
#guard canon ("1.5e-" ++ String.ofList (List.replicate 5000 '0') ++ "3") == "0.0015"
#guard canon ("1e" ++ String.ofList (List.replicate 30 '9')) == "error: at byte 0: a float beyond the range of binary64"
-- `tomljson%` is normal, whatever its literals; an identifier key is its name
#guard (tomljson% [1e400, {b: 1, a: 2, a: 3}]).isNormal
#guard (tomljson% {«a b»: 1, «1»: 2}).render == "{\"1\":2,\"a b\":1}"
/-- `tomljson%` inside a macro: hygiene must not reach the keys. -/
macro "keysInMacro" : term => `(tomljson% {foo: 1, "bar": 2})
#guard (keysInMacro).render == "{\"bar\":2,\"foo\":1}"

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
