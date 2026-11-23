import TomlJson

/-! # `tomljson check`: is this canonical JSON Lines?

```
tomljson check < records.jsonl
```

Exits 0 when every line is a canonical text (see `SPEC.md`), each ended by a line feed, and 1 at
the first line that is not, with the byte where it departs from canonical form.
-/

open TomlJson

/-- Usage text. -/
def usage : String :=
  "usage: tomljson check < input.jsonl\n" ++
  "  exit 1 at the first line that is not canonical JSON Lines\n"

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

/-- Run the subcommand. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["check"] =>
    match (← readStdin) >>= Value.parseLines with
    | .ok values =>
      IO.eprintln s!"tomljson: {values.size} canonical lines"
      return 0
    | .error e =>
      IO.eprintln s!"tomljson: {e}"
      return 1
  | _ =>
    IO.eprint usage
    return 2
