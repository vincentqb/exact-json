module

import ExactJSON.Codec

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

def typedCheck : String → Option (String → Except String Nat)
  | "Value" => some fun (s : String) => (decodeLines (α := Value) s).map (·.size)
  | "String" => some fun (s : String) => (decodeLines (α := String) s).map (·.size)
  | "Bool" => some fun (s : String) => (decodeLines (α := Bool) s).map (·.size)
  | "Int" => some fun (s : String) => (decodeLines (α := Int) s).map (·.size)
  | "Nat" => some fun (s : String) => (decodeLines (α := Nat) s).map (·.size)
  | "UInt8" => some fun (s : String) => (decodeLines (α := UInt8) s).map (·.size)
  | "UInt16" => some fun (s : String) => (decodeLines (α := UInt16) s).map (·.size)
  | "UInt32" => some fun (s : String) => (decodeLines (α := UInt32) s).map (·.size)
  | "UInt64" => some fun (s : String) => (decodeLines (α := UInt64) s).map (·.size)
  | "Int8" => some fun (s : String) => (decodeLines (α := Int8) s).map (·.size)
  | "Int16" => some fun (s : String) => (decodeLines (α := Int16) s).map (·.size)
  | "Int32" => some fun (s : String) => (decodeLines (α := Int32) s).map (·.size)
  | "Int64" => some fun (s : String) => (decodeLines (α := Int64) s).map (·.size)
  | "Float" => some fun (s : String) => (decodeLines (α := Float) s).map (·.size)
  | "Char" => some fun (s : String) => (decodeLines (α := Char) s).map (·.size)
  | "Array Nat" => some fun (s : String) => (decodeLines (α := Array Nat) s).map (·.size)
  | "List Nat" => some fun (s : String) => (decodeLines (α := List Nat) s).map (·.size)
  | "Nat × String" => some fun (s : String) => (decodeLines (α := Nat × String) s).map (·.size)
  | "Option Nat" => some fun (s : String) => (decodeLines (α := Option Nat) s).map (·.size)
  | "TreeMap String Nat" => some fun (s : String) => (decodeLines (α := Std.TreeMap String Nat) s).map (·.size)
  | "HashMap String Nat" => some fun (s : String) => (decodeLines (α := Std.HashMap String Nat) s).map (·.size)
  | _ => none

def canon (lines : Bool) (input : String) : Except String String := do
  if !lines then
    let v ← Value.readJson input
    return v.render.push '\n'
  let parts := input.splitOn "\n"
  let mut out := ""
  for line in parts, k in [0:parts.length] do
    if k + 1 == parts.length && line.isEmpty then break
    match Value.readJson line with
    | .ok v => out := (Value.renderTo out v).push '\n'
    | .error e => throw s!"line {k + 1}, {e}"
  return out

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
      | [] => some fun (s : String) => (decodeLines (α := Value) s).map Array.size
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
