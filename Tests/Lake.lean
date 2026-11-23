module

import TomlJsonLake
meta import TomlJsonLake

/-! Lake's TOML values as `Value`s and back, checked when this module is built (`lake test`). -/

open TomlJson

/-- A TOML document with every kind of value. -/
def document : String := "
title = \"TOML \\\"example\\\"\\t\\u00e9\"
int = [+99, 0xDEAD_BEEF, 0o755, 0b1101, -17, 1_000]
float = [1.0, 3.1415, -0.01, 5e+22, 1e-7, -0.0, inf, -inf, nan]
bool = [true, false]
odt = [1979-05-27T07:32:00Z, 1979-05-27T00:32:00.999999-07:00, 1979-05-27 07:32:00+00:00]
ldt = 1979-05-27T07:32:00.5
ld = 1979-05-27
lt = [07:32:00, 00:32:00.123456789123, 00:00:00.05]
site.\"google.com\" = true
inline = { x = 1, y = { z = [] } }

[[points]]
x = 1

[[points]]
x = 2
"

/-- Its canonical JSON. -/
def expected : String :=
  "{\"bool\":[true,false]," ++
  "\"float\":[1.0,3.1415,-0.01,5.0e22,1.0e-7,-0.0,\"Infinity\",\"-Infinity\",\"NaN\"]," ++
  "\"inline\":{\"x\":1,\"y\":{\"z\":[]}}," ++
  "\"int\":[99,3735928559,493,13,-17,1000]," ++
  "\"ld\":\"1979-05-27\",\"ldt\":\"1979-05-27T07:32:00.5\"," ++
  "\"lt\":[\"07:32:00\",\"00:32:00.123456789\",\"00:00:00.05\"]," ++
  "\"odt\":[\"1979-05-27T07:32:00Z\",\"1979-05-27T00:32:00.999999-07:00\",\"1979-05-27T07:32:00Z\"]," ++
  "\"points\":[{\"x\":1},{\"x\":2}]," ++
  "\"site\":{\"google.com\":true}," ++
  "\"title\":\"TOML \\\"example\\\"\\té\"}"

#eval show IO Unit from do
  match ← ofTomlText document with
  | .error e => throw (IO.userError e)
  | .ok v =>
    unless v.render == expected do
      throw (IO.userError s!"TOML as JSON:\n{v.render}\nexpected:\n{expected}")
    -- and back: Lake's values give the same canonical JSON
    unless (Value.ofToml v.toToml).render == expected do
      throw (IO.userError "Value.toToml loses something")

-- date-times through Lake's types
#guard ["1979-05-27T07:32:00Z", "1979-05-27T00:32:00.999999-07:00", "1979-05-27T07:32:00.5",
  "1979-05-27", "07:32:00", "23:59:60.25", "00:00:00.05", "00:00:00.000000001"].all fun s =>
  (DateTime.parse? s).map (fun dt => (DateTime.ofLake dt.toLake).toString) == some s

-- a malformed document is Lake's error
#eval show IO Unit from do
  match ← ofTomlText "a = \"x\"\na = 2\n" with
  | .ok v => throw (IO.userError s!"a duplicate key was accepted: {v.render}")
  | .error _ => pure ()
