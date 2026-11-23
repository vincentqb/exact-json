module

public import TomlJson.Float
public import TomlJson.Value
public import TomlJson.Render
public import TomlJson.Parse
public import TomlJson.Codec
public import TomlJson.DateTime
public import TomlJson.Derive
public import TomlJson.Literal
public import TomlJson.LeanJson

/-! # TomlJson

Canonical, strictly typed JSON: one line of ordinary JSON per value, under the law
`decode s = .ok a ↔ encode a = s`. See `SPEC.md`.
-/
