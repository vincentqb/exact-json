module

public import TomlJson.Float
public import TomlJson.Value
public import TomlJson.Render
public import TomlJson.Parse
public import TomlJson.Class
public import TomlJson.DateTime
public import TomlJson.Derive
public import TomlJson.Literal
public import TomlJson.LeanJson

/-! # TomlJson

Canonical JSON for TOML-typed data: one line of JSON per value, which every JSON reader reads as
usual, and which Lean reads back and writes again to the same bytes. See `SPEC.md`.
-/
