import TomlJson

/-! # `tomljson`: canonicalize and check JSON Lines

```
tomljson canon   < any.jsonl   > canonical.jsonl   # read leniently, write canonical lines
tomljson check   < some.jsonl                      # fail unless every line is canonical
```
-/

open TomlJson

/-- Usage text. -/
def usage : String :=
  "usage: tomljson (canon | check) < input.jsonl\n" ++
  "  canon  read JSON Lines leniently (any JSON per line), write canonical JSON Lines\n" ++
  "  check  exit 1 at the first line that is not canonical JSON Lines\n"

/-- Standard input, as UTF-8 text. -/
def readStdin : IO String := do
  let stdin ← IO.getStdin
  let mut bytes := ByteArray.empty
  repeat
    let chunk ← stdin.read 65536
    if chunk.isEmpty then break
    bytes := bytes ++ chunk
  match String.fromUTF8? bytes with
  | some s => return s
  | none => throw (IO.userError "input is not UTF-8")

/-- Run a subcommand. -/
def main (args : List String) : IO UInt32 := do
  match args with
  | ["canon"] =>
    match Value.parseLines (← readStdin) with
    | .ok values =>
      (← IO.getStdout).putStr (Value.renderLines values)
      return 0
    | .error e =>
      IO.eprintln s!"tomljson: {e}"
      return 1
  | ["check"] =>
    match Value.parseLinesCanonical (← readStdin) with
    | .ok values =>
      IO.eprintln s!"tomljson: {values.size} canonical lines"
      return 0
    | .error e =>
      IO.eprintln s!"tomljson: {e}"
      return 1
  | _ =>
    IO.eprint usage
    return 2
