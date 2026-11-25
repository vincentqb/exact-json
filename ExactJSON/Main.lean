module

public import ExactJSON.Codec
public import ExactJSON.DateTime
public import ExactJSON.ShapesDerived

open ExactJSON

def usage : String :=
  "usage: exactjson check [--depth N] [--value] [--as TYPE] < input.jsonl\n" ++
  "  exit 1 at the first line that is not canonical JSON Lines (of a value of TYPE)\n" ++
  "  with --value, unless the input is the canonical text of one value (of TYPE)\n" ++
  "       exactjson canon [--depth N] [--lines] < input.json\n" ++
  "  write the canonical text of the JSON text (or of each line)\n" ++
  "  values nested deeper than N (by default 1000) are rejected\n"

def readValue (sp : Spelling) (maxDepth : Nat) : IO (Except String Value) := do
  let stdin ← IO.getStdin
  let mut reader := Reader.start sp maxDepth
  repeat
    let chunk ← stdin.read 65536
    if chunk.isEmpty then break
    reader := chunk.foldl Reader.step reader
  return reader.finish

def readBytes : IO ByteArray := do
  let stdin ← IO.getStdin
  let mut bytes := ByteArray.empty
  repeat
    let chunk ← stdin.read 65536
    if chunk.isEmpty then break
    bytes := bytes ++ chunk
  return bytes

public section

def checkAs (α : Type) [ToValue α] [FromValue α] (value : Bool) (maxDepth : Nat) (b : ByteArray) :
    Except String Nat :=
  if value then (decode (α := α) maxDepth b).map fun _ => 1
  else do
    let as ← decodeLines (α := α) maxDepth b
    if (encodeLines as).toUTF8 == b then pure as.size else throw "the decoded lines are written differently"

def typedCheck : String → Option (Bool → Nat → ByteArray → Except String Nat)
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
  | "Decimal" => some (checkAs Decimal)
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

def depthFlag : List String → Option (Nat × List String)
  | "--depth" :: n :: rest => n.toNat?.map fun d => (d, rest)
  | rest => some (1000, rest)

def finish (result : Except String Nat) : IO UInt32 := do
  match result with
  | .ok count =>
    IO.eprintln s!"exactjson: {count} canonical {if count == 1 then "text" else "texts"}"
    return 0
  | .error e =>
    IO.eprintln s!"exactjson: {e}"
    return 1

def main (args : List String) : IO UInt32 := do
  match args with
  | "canon" :: flags =>
    let some (maxDepth, flags) := depthFlag flags | do IO.eprint usage; return 2
    let some lines := (match flags with
      | [] => some false
      | ["--lines"] => some true
      | _ => none)
      | do IO.eprint usage; return 2
    let result : Except String String ←
      if lines then pure ((Value.readLines .any maxDepth (← readBytes)).map Value.renderLines)
      else pure ((← readValue .any maxDepth).map fun v => Value.renderLines #[v])
    match result with
    | .ok text =>
      IO.print text
      return 0
    | .error e =>
      IO.eprintln s!"exactjson: {e}"
      return 1
  | "check" :: flags =>
    let some (maxDepth, flags) := depthFlag flags | do IO.eprint usage; return 2
    let (value, flags) := match flags with
      | "--value" :: rest => (true, rest)
      | rest => (false, rest)
    match flags with
    | [] =>
      if value then finish ((← readValue .canonical maxDepth).map fun _ => 1)
      else finish ((Value.readLines .canonical maxDepth (← readBytes)).map Array.size)
    | ["--as", type] =>
      match typedCheck type with
      | some check => finish (check value maxDepth (← readBytes))
      | none => do IO.eprint usage; return 2
    | _ => do IO.eprint usage; return 2
  | _ =>
    IO.eprint usage
    return 2

end
