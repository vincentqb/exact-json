module

public import ExactJSON.Float
public import ExactJSON.Value
public import ExactJSON.Render
public import ExactJSON.Parse
public import ExactJSON.Codec
public import ExactJSON.DateTime
public import ExactJSON.Derive
public import ExactJSON.Literal
public import ExactJSON.LeanJson

/-! # ExactJSON

Canonical, strictly typed JSON: one line of ordinary JSON per value, under the law
`decode s = .ok a ↔ encode a = s`. See `SPEC.md`.
-/
