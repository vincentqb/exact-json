module

import ExactJSON
meta import ExactJSON

open ExactJSON

def parseText (s : String) : Except String Value := Value.read .canonical 10000 s.toUTF8

def readText (s : String) : Except String Value := Value.read .any 10000 s.toUTF8

def decodeText {α : Type} [ToValue α] [FromValue α] (s : String) : Except String α := decode 10000 s.toUTF8

def linesText (s : String) : Except String (Array Value) := Value.readLines .canonical 10000 s.toUTF8

def check (s : String) : String :=
  match parseText s with
  | .ok v => if v.render == s then "ok" else s!"read, but written back as {v.render}"
  | .error e => e

def gives {α : Type} [BEq α] (e : Except String α) (x : α) : Bool :=
  match e with
  | .ok y => y == x
  | .error _ => false

def errorOf {α : Type} (e : Except String α) : String :=
  match e with
  | .ok _ => "ok"
  | .error e => e

#guard ["null", "true", "false", "0", "-17", "123456789012345678901234567890", "1.0", "-0.0", "0.1",
  "1.5e-7", "1.0e16", "5.0e-324", "1.7976931348623157e308", "\"\"", "\"a\\tb\"", "[]", "{}",
  "[1,2.5,\"x\",null,[],{}]", "{\"a\":{\"b\":[null]},\"b\":1}"].all (check · == "ok")
#guard check "1e5" == "at character 0: not the canonical text of this decimal: write 100000.0"
#guard check "1.50" == "at character 0: not the canonical text of this decimal: write 1.5"
#guard check "1.0e+16" == "at character 0: not the canonical text of this decimal: write 1.0e16"
#guard check "0.00001" == "at character 0: not the canonical text of this decimal: write 1.0e-5"
#guard check "1e16" == "at character 0: not the canonical text of this decimal: write 1.0e16"
#guard ["0.1000000000000000055511151231257827", "9007199254740993.0", "1.0e400", "-1.0e-400",
  "1.2345678901234567890123456789e-5000"].all (check · == "ok")
#guard check "-0" == "at character 0: not the canonical text of this integer: write 0"
#guard check "01" == "at character 0: not the canonical text of this integer: write 1"
#guard check "-01" == "at character 0: not the canonical text of this integer: write -1"
#guard check "00.5" == "at character 0: not the canonical text of this decimal: write 0.5"
#guard check "1e400" == "at character 0: not the canonical text of this decimal: write 1.0e400"
#guard check ("1e" ++ String.ofList (List.replicate 5000 '0') ++ "1") ==
  "at character 0: not the canonical text of this decimal: write 10.0"
#guard check ("1e" ++ String.ofList (List.replicate 2000 '9')) ==
  "at character 0: not the canonical text of this decimal: write 1.0e" ++ String.ofList (List.replicate 2000 '9')
#guard check ("1e-" ++ String.ofList (List.replicate 2000 '9')) ==
  "at character 0: not the canonical text of this decimal: write 1.0e-" ++ String.ofList (List.replicate 2000 '9')
#guard check ("0.0e" ++ String.ofList (List.replicate 100000 '9')) ==
  "at character 0: not the canonical text of this decimal: write 0.0"
#guard check " 1" == "at character 0: canonical text has no whitespace"
#guard check "[1, 2]" == "at character 3: canonical text has no whitespace"
#guard check "{\"a\": 1}" == "at character 5: canonical text has no whitespace"
#guard check "1\n" == "at character 1: text after the value (canonical text has no whitespace)"

#guard Value.render (.string "tab\t nl\n cr\r bs\x08 ff\x0c q\" bsl\\ nul\x00 us\x1f") ==
  "\"tab\\t nl\\n cr\\r bs\\b ff\\f q\\\" bsl\\\\ nul\\u0000 us\\u001f\""
#guard Value.render (.string "\x7f\u0085\u009b\u2028\u2029/é😀\u200d\ufe0f") ==
  "\"\\u007f\\u0085\\u009b\\u2028\\u2029/é😀\u200d\ufe0f\""
#guard check "\"\\u007f\\u0085\\u2028\\u2029\"" == "ok"
#guard check "\"\x7f\"" == "at character 1: write \\u007f, not the character itself"
#guard check "\"a\u0085\"" == "at character 2: write \\u0085, not the character itself"
#guard check "\"\u2028\"" == "at character 1: write \\u2028, not the character itself"
#guard check "\"\\u009B\"" == "at character 1: write \\u009b, not \\u009B"
#guard check "\"\\/\"" == "at character 1: write /, not \\/"
#guard check "\"\\u0041\"" == "at character 1: write A, not \\u0041"
#guard check "\"\\u0100\"" == "at character 1: write Ā, not \\u0100"
#guard check "\"\\u000a\"" == "at character 1: write \\n, not \\u000a"
#guard check "\"\\u0022\"" == "at character 1: write \\\", not \\u0022"
#guard check "\"\\u001F\"" == "at character 1: write \\u001f, not \\u001F"
#guard check "\"\\ud83d\\ude00\"" == "at character 1: write 😀, not the surrogate pair \\ud83d\\ude00"
#guard check "\"\\udc00\"" == "at character 1: \\udc00 is a lone surrogate, not a character"
#guard check "\"a\tb\"" == "at character 2: write \\t, not the character itself"

#guard check ("{\"B\":1,\"a\":2,\"" ++ String.singleton (Char.ofNat 0xFFFF) ++ "\":3,\"" ++
  String.singleton (Char.ofNat 0x10000) ++ "\":4}") == "ok"
#guard check "{\"b\":1,\"a\":2}" == "at character 7: keys must increase: \"a\" comes before \"b\""
#guard check "{\"a\":1,\"a\":2}" == "at character 7: duplicate key \"a\""
#guard check "{\"a\":null}" == "ok"

#guard ["", "{", "[1,]", "[,1]", "{\"a\":1,}", "1.", ".5", "-", "1e", "+1", "tru", "nul",
  "[1 2]", "{}x", "'a'", "{1:2}", "NaN", "Infinity", "\"\\x\"", "0x10", "1_000"].all
  fun s => !(parseText s).isOk

#guard (Value.table #[("b", .integer 1), ("a", .integer 2)]).render == "{\"b\":1,\"a\":2}"
#guard !(Value.table #[("b", .integer 1), ("a", .integer 2)]).isValid
#guard (Value.decimal ⟨false, 150, -2⟩).render == "1.50"
#guard !(Value.decimal ⟨false, 150, -2⟩).isValid
#guard !(parseText (Value.array #[.decimal ⟨false, 150, -2⟩]).render).isOk
#guard (Value.decimal ⟨false, 10, 0⟩).render == (Value.decimal ⟨false, 1, 1⟩).render
#guard gives (parseText "0.1000000000000000055511151231257827")
  (.decimal ⟨false, 1000000000000000055511151231257827, -34⟩)
#guard gives (parseText "-0.0") (.decimal ⟨true, 0, 0⟩)
#guard gives (parseText "1.0e400") (.decimal ⟨false, 1, 400⟩)
#guard gives (decodeText "0.1" : Except String Float) 0.1
#guard errorOf (decodeText "0.1000000000000000055511151231257827" : Except String Float) ==
  "expected the shortest decimal of a float: write 0.1, not 0.1000000000000000055511151231257827"
#guard errorOf (decodeText "9007199254740993.0" : Except String Float) ==
  "expected the shortest decimal of a float: write 9007199254740992.0, not 9007199254740993.0"
#guard errorOf (decodeText "1.0e400" : Except String Float) == "a float beyond the range of binary64: 1.0e400"
#guard errorOf (decodeText "1.0e-400" : Except String Float) ==
  "expected the shortest decimal of a float: write 0.0, not 1.0e-400"

#guard check "[[[[" == "at character 4: expected a value, found the end of the text"
#guard check "{\"a\":[{\"b\":" == "at character 11: expected a value, found the end of the text"
#guard check (String.ofList (List.replicate 2000 '[' ++ List.replicate 2000 ']')) == "ok"
#guard check (String.ofList (List.replicate 2000 '[')) ==
  "at character 2000: expected a value, found the end of the text"

def canon (s : String) : String :=
  match readText s with
  | .ok v => v.render
  | .error e => e

#guard canon " {\"b\" : [1, 2.50, -0, 1E+2, 1e-2, 0.5e1], \"a\":\t\"\\u00e9\\/\\ud83d\\ude00\\n\"}\r\n" ==
  "{\"a\":\"é/😀\\n\",\"b\":[1,2.5,0,100.0,0.01,5.0]}"
#guard canon "[ ]" == "[]"
#guard canon "{ }" == "{}"
#guard ["null", "true", "-17", "1.0e16", "[1,2.5,\"x\",{}]", "{\"a\":{\"b\":[null]},\"b\":1}"].all
  fun s => canon s == s
#guard ["", " ", "[1,]", "{\"a\":1,}", "01", "-01", "-", "1.", ".5", "+1", "1e", "NaN", "Infinity", "'a'",
  "[1 2]", "{\"a\" 1}", "{a:1}", "\"\t\"", "\"\\x\"", "\"\\u12\"", "// c\n1", "\ufeff1", "tru", "1 2",
  "[", "{\"a\":1", "\"a", "0x10"].all fun s => !(readText s).isOk
#guard canon "{\"a\":1,\"a\":2}" == "at character 7: a key repeats"
#guard canon "\"\\udc00\"" == "at character 1: a low surrogate not after a high one"
#guard canon "\"\\ud800x\"" == "at character 1: a high surrogate not followed by a low one"
#guard canon "1e400" == "1.0e400"
#guard canon "[1,]" == "at character 3: expected a value"

#guard gives ((linesText "{\"a\":1}\n[2]\n").map (·.map Value.render)) #["{\"a\":1}", "[2]"]
#guard gives ((linesText "").map (·.size)) 0
#guard errorOf (linesText "{\"a\":1}\n[2]") == "the last line has no line feed at its end"
#guard errorOf (linesText "1\n[\n3") == "the last line has no line feed at its end"
#guard errorOf (linesText "1\n[\n3\n") == "line 2: at character 1: expected a value, found the end of the text"
#guard errorOf (linesText "1\n\n2\n") == "line 2: at character 0: expected a value, found the end of the text"
#guard errorOf (linesText "1\r\n") == "line 1: at character 1: text after the value (canonical text has no whitespace)"


structure Run where
  name : String
  iters : Nat
  time? : Option Float
  day : LocalDate
  deriving ToValue, FromValue

def run : Run := { name := "a", iters := 3, time? := some 2.0, day := { year := 2024, month := 2, day := 29 } }

#guard encode run == "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"time\":2.0}"
#guard encode { run with time? := none } == "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\"}"
#guard gives ((decodeText (encode run) : Except String Run).map encode) (encode run)
#guard gives ((decodeText (encode { run with time? := none }) : Except String Run).map encode)
  (encode { run with time? := none })
#guard errorOf (decodeText "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"time\":2}" : Except String Run) ==
  "time: expected a float, found integer 2"
#guard errorOf (decodeText "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"x\":0}" : Except String Run) ==
  "Run has no field \"x\""
#guard errorOf (decodeText "{\"day\":\"2024-02-29\",\"iters\":3,\"name\":\"a\",\"time\":null}" : Except String Run) ==
  "time: expected a float, found null null"
#guard errorOf (decodeText "{\"day\":\"2024-02-29\",\"name\":\"a\"}" : Except String Run) == "missing key \"iters\""
#guard errorOf (decodeText "{\"day\":\"2023-02-29\",\"iters\":1,\"name\":\"a\"}" : Except String Run) ==
  "day: expected a date-time, date or time in canonical RFC 3339 form, found string \"2023-02-29\""

#guard encode #[some 1, none, some 3] == "[1,null,3]"
#guard gives (decodeText "[1,null,3]" : Except String (Array (Option Nat))) #[some 1, none, some 3]

structure Twice where
  x : Option (Option Nat)
  deriving ToValue, FromValue

#guard [({ x := none } : Twice), { x := some none }, { x := some (some 2) }].map encode ==
  ["{}", "{\"x\":null}", "{\"x\":2}"]
#guard ["{}", "{\"x\":null}", "{\"x\":2}"].all fun s =>
  gives ((decodeText s : Except String Twice).map encode) s

structure Box (α : Type) where
  x : α
  deriving ToValue, FromValue

inductive Leaf (α : Type) where
  | leaf (x : α)
  deriving ToValue, FromValue

#guard encode ({ x := none } : Box (Option Nat)) == "{\"x\":null}"
#guard encode ({ x := some 1 } : Box (Option Nat)) == "{\"x\":1}"
#guard (decodeText "{\"x\":null}" : Except String (Box (Option Nat))).isOk
#guard !(decodeText "{}" : Except String (Box (Option Nat))).isOk
#guard encode (Leaf.leaf (none : Option Nat)) == "{\"leaf\":{\"x\":null}}"
#guard encode ({ x := 3 } : Box Nat) == "{\"x\":3}"

inductive Shape where
  | circle (radius : Float)
  | rect (w h : Float)
  | pair : Nat → String → Shape
  | dot
  deriving ToValue, FromValue

#guard [Shape.circle 1, .rect 2 0.5, .pair 7 "s", .dot].map encode ==
  ["{\"circle\":{\"radius\":1.0}}", "{\"rect\":{\"h\":0.5,\"w\":2.0}}", "{\"pair\":[7,\"s\"]}", "\"dot\""]
#guard errorOf (decodeText "{\"rect\":{\"w\":1.0}}" : Except String Shape) == "rect: missing key \"h\""
#guard errorOf (decodeText "{\"circle\":{\"r\":1.0,\"radius\":1.0}}" : Except String Shape) ==
  "circle: circle has no field \"r\""
#guard errorOf (decodeText "\"square\"" : Except String Shape) == "unknown constructor \"square\""

inductive Cmd where
  | run (verbose? : Option Bool) (level? : Option Nat)
  | stop
  deriving ToValue, FromValue

#guard ["{\"run\":5}", "{\"run\":\"x\"}", "{\"run\":[true]}"].all fun s => !(decodeText s : Except String Cmd).isOk
#guard (decodeText "{\"run\":{}}" : Except String Cmd).isOk

#guard encode #[1.0 / 0.0, -1.0 / 0.0, 0.0 / 0.0, -0.0] == "[\"Infinity\",\"-Infinity\",\"NaN\",-0.0]"
#guard gives ((decodeText "[\"Infinity\",-0.0]" : Except String (Array Float)).map fun xs => xs.map (·.toBits))
  #[(1.0 / 0.0 : Float).toBits, (-0.0 : Float).toBits]
#guard !(decodeText "256" : Except String UInt8).isOk
#guard gives ((decodeText "-128" : Except String Int8).map (·.toInt)) (-128)

#guard ["1979-05-27T07:32:00Z", "1979-05-27T00:32:00.999999-07:00", "1979-05-27T07:32:00.5",
  "1979-05-27", "07:32:00", "23:59:60", "00:00:00.000000001"].all fun s =>
  (DateTime.parse? s).map DateTime.toString == some s
#guard ["1979-05-27t07:32:00Z", "1979-05-27 07:32:00Z", "1979-05-27T07:32:00z",
  "1979-05-27T07:32:00+00:00", "1979-05-27T07:32", "07:32:00.50", "07:32:00.5000000001",
  "2024-13-01", "2023-02-29", "24:00:00", "1979-05-27T07:32:00+24:00", "1979-5-27"].all
  fun s => (DateTime.parse? s).isNone


structure Bench where
  name : String
  iters : Nat
  time? : Option Float
  day : LocalDate
  deriving ToValue, FromValue, Repr

/-- info: {"day":"2024-02-29","iters":100,"name":"fast","time":2.0} -/
#guard_msgs in
#eval IO.println (encode ({ name := "fast", iters := 100, time? := some 2.0, day := { year := 2024, month := 2, day := 29 } } : Bench))

/-- info: Except.error "missing key \"day\"" -/
#guard_msgs in
#eval (decodeText "{\"iters\":100,\"name\":\"fast\"}" : Except String Bench)
#guard (decodeText "{\"day\":\"2024-02-29\",\"iters\":100,\"name\":\"fast\"}" : Except String Bench).isOk
#guard errorOf (decodeText "{\"iters\":100,\"name\":\"fast\"}" : Except String Bench) == "missing key \"day\""

#guard errorOf (Value.read .canonical 1 "[[1]]".toUTF8) == "nested deeper than 1"
#guard gives (Value.read .canonical 2 "[[1]]".toUTF8) (.array #[.array #[.integer 1]])
#guard gives (Value.read .canonical 0 "1".toUTF8) (.integer 1)
#guard errorOf (Value.read .any 100 (String.ofList (List.replicate 100000 '[')).toUTF8) == "nested deeper than 100"
#guard errorOf (Value.read .any 100 ("\"" ++ String.ofList (List.replicate 1000 '[') ++ "\"").toUTF8) == "ok"
#guard errorOf (Value.read .any 10 ⟨#[0x22, 0xFF, 0x22]⟩) == "not UTF-8"
#guard gives (Value.read .any 10 " [ 1 , 2.50 ] ".toUTF8) (.array #[.integer 1, .decimal ⟨false, 25, -1⟩])
#guard !(Value.read .canonical 10 " [ 1 , 2.50 ] ".toUTF8).isOk
#guard gives (("2]".toUTF8.foldl Reader.step ("[1,".toUTF8.foldl Reader.step (Reader.start .canonical 10))).finish)
  (.array #[.integer 1, .integer 2])
#guard gives ((Value.readLines .any 10 " 1 \r\n{ }\n".toUTF8).map (·.map Value.render)) #["1", "{}"]
#guard !(Value.readLines .canonical 10 " 1 \r\n{ }\n".toUTF8).isOk
