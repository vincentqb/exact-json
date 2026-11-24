module

public import ExactJSON.Codec
public import ExactJSON.DateTime
public import ExactJSON.ShapesDerived

open ExactJSON

def usage : String :=
  "usage: exactjson check [--as TYPE] < input.jsonl\n" ++
  "  exit 1 at the first line that is not canonical JSON Lines (of a value of TYPE)\n" ++
  "       exactjson canon [--lines] < input.json\n" ++
  "  write the canonical text of the JSON text (or of each line)\n"

def readStdin : IO (Except String String) := do
  let stdin ← IO.getStdin
  let mut bytes := ByteArray.empty
  repeat
    let chunk ← stdin.read 65536
    if chunk.isEmpty then break
    bytes := bytes ++ chunk
  match String.fromUTF8? bytes with
  | some s => return .ok s
  | none =>
    let mut start := 0
    let mut line := 1
    for i in [0:bytes.size + 1] do
      if i == bytes.size || bytes[i]! == 0x0A then
        if (String.fromUTF8? (bytes.extract start i)).isNone then
          return .error s!"line {line}: not UTF-8"
        start := i + 1
        line := line + 1
    return .error "not UTF-8"

public section

def textLines (s : String) : List String :=
  let parts := s.splitOn "\n"
  if parts.getLast? = some "" then parts.dropLast else parts

def readEach (number : Nat) (out : Array Value) : List String → Except String (Array Value)
  | [] => .ok out
  | line :: rest =>
    match Value.readJson line with
    | .error e => .error s!"line {number + 1}, {e}"
    | .ok v => readEach (number + 1) (out.push v) rest

def canon (lines : Bool) (input : String) : Except String String :=
  if lines then (readEach 0 #[] (textLines input)).map Value.renderLines
  else (Value.readJson input).map fun v => Value.renderLines #[v]

def checkAs (α : Type) [ToValue α] [FromValue α] (s : String) : Except String Nat := do
  let as ← decodeLines (α := α) s
  if encodeLines as == s then pure as.size else throw "the decoded lines are written differently"

def typedCheck : String → Option (String → Except String Nat)
  | "String" => some (checkAs String)
  | "Bool" => some (checkAs Bool)
  | "Int" => some (checkAs Int)
  | "Nat" => some (checkAs Nat)
  | "UInt8" => some (checkAs (UInt8))
  | "UInt16" => some (checkAs (UInt16))
  | "UInt32" => some (checkAs (UInt32))
  | "UInt64" => some (checkAs (UInt64))
  | "Int8" => some (checkAs (Int8))
  | "Int16" => some (checkAs (Int16))
  | "Int32" => some (checkAs (Int32))
  | "Int64" => some (checkAs (Int64))
  | "Float" => some (checkAs Float)
  | "Char" => some (checkAs Char)
  | "Array Nat" => some (checkAs (Array Nat))
  | "List Nat" => some (checkAs (List Nat))
  | "Nat × String" => some (checkAs (Nat × String))
  | "Option Nat" => some (checkAs (Option Nat))
  | "ExtTreeMap String Nat" => some (checkAs (Std.ExtTreeMap String Nat))
  | "LocalDate" => some (checkAs LocalDate)
  | "LocalTime" => some (checkAs LocalTime)
  | "LocalDateTime" => some (checkAs LocalDateTime)
  | "OffsetDateTime" => some (checkAs OffsetDateTime)
  | "DateTime" => some (checkAs DateTime)
  | "Example.Point" => some (checkAs Example.Point)
  | "Example.Shape" => some (checkAs Example.Shape)
  | "Example.Envelope" => some (checkAs Example.Envelope)
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | "canon" :: flags =>
    let lines ← match flags with
      | [] => pure false
      | ["--lines"] => pure true
      | _ => do IO.eprint usage; return 2
    match (← readStdin) >>= canon lines with
    | .ok text =>
      IO.print text
      return 0
    | .error e =>
      IO.eprintln s!"exactjson: {e}"
      return 1
  | "check" :: flags =>
    let some decodeAll := (match flags with
      | [] => some fun (s : String) => (Value.parseLines s).map Array.size
      | ["--as", type] => typedCheck type
      | _ => none)
      | do IO.eprint usage; return 2
    match (← readStdin) >>= decodeAll with
    | .ok count =>
      IO.eprintln s!"exactjson: {count} canonical lines"
      return 0
    | .error e =>
      IO.eprintln s!"exactjson: {e}"
      return 1
  | _ =>
    IO.eprint usage
    return 2

end
