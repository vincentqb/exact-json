module

import ExactJSON.Codec

/-! # `exactjson check` and `exactjson canon`

```
exactjson check < records.jsonl
exactjson canon < any.json
exactjson canon --lines < any.jsonl
```

`check` exits 0 when every line is a canonical text, each ended by a line feed, and
1 at the first line that is not, with the character where it departs from canonical form.

`canon` reads its input as one JSON text (RFC 8259), in any spelling, and writes the canonical
text of the value it holds, and a line feed; with `--lines`, it does so for each line. It exits 1
at the first text that is not read, saying why and where.
-/

open ExactJSON

/-- Usage text. -/
def usage : String :=
  "usage: exactjson check < input.jsonl\n" ++
  "  exit 1 at the first line that is not canonical JSON Lines\n" ++
  "       exactjson canon [--lines] < input.json\n" ++
  "  write the canonical text of the JSON text (or of each line)\n"

/-- Standard input, as UTF-8 text, or the first line that is not UTF-8. -/
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
    -- find the line: split at line feeds, which UTF-8 never holds inside a character
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

/-- The canonical text of each JSON text, each with a line feed, or the first that is not read:
`input` is one text, or with `lines` one text a line. -/
def canon (lines : Bool) (input : String) : Except String String := do
  if !lines then
    let v ← Value.readJson input
    return v.render.push '\n'
  let parts := input.splitOn "\n"
  let mut out := ""
  for line in parts, k in [0:parts.length] do
    -- after the final line feed, nothing
    if k + 1 == parts.length && line.isEmpty then break
    match Value.readJson line with
    | .ok v => out := (Value.renderTo out v).push '\n'
    | .error e => throw s!"line {k + 1}, {e}"
  return out

/-- Run the subcommand: `check` reads every line as a `Value` through `decode`, and `canon` reads
JSON through `Value.readJson`; between them they go through every function the challenge states
something about. -/
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
  | ["check"] =>
    match (← readStdin) >>= (decodeLines (α := Value) ·) with
    | .ok values =>
      IO.eprintln s!"exactjson: {values.size} canonical lines"
      return 0
    | .error e =>
      IO.eprintln s!"exactjson: {e}"
      return 1
  | _ =>
    IO.eprint usage
    return 2

end
