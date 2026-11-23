# lean-toml-json

Canonical, strictly typed JSON for Lean. A value is written as one line of ordinary JSON, which any
JSON reader parses, and Lean reads it back under one law:

```
decode s = .ok a   ↔   encode a = s
```

Reading undoes writing, each value has exactly one text, and no other text is read: no
whitespace, no other number spelling, no integer for a float, no unknown key. Integers never have
a point and floats always do, `none` is an absent key as a field and `null` elsewhere, date-times
are RFC 3339 strings. The format is specified in [`SPEC.md`](SPEC.md), and its laws are stated
as theorems in [`Challenge.lean`](Challenge.lean) (see [The laws](#the-laws)).

```lean
import TomlJson
open TomlJson

structure Bench where
  name : String
  iters : Nat
  time? : Option Float     -- an optional key: absent when `none`
  day : LocalDate          -- the string "2024-02-29"
  deriving ToValue, FromValue, Repr

#eval IO.println (encode ({ name := "fast", iters := 100, time? := some 2.0, day := ⟨2024, 2, 29⟩ } : Bench))
-- {"day":"2024-02-29","iters":100,"name":"fast","time":2.0}

#eval (decode "{\"iters\":100,\"name\":\"fast\"}" : Except String Bench)
-- Except.error "missing key \"day\""
```

## `none` and `null`

| Lean                             | JSON                                          |
|----------------------------------|-----------------------------------------------|
| field `x : Option α`             | key absent for `none`, `"x":…` for `some a`   |
| field `x : Option (Option α)`    | absent, `"x":null`, or `"x":…`                |
| `Array (Option α)`, top level, … | `null` for `none`: `[1,null,3]`               |

`Option (Option α)` outside a field is a compile error, since `none` and `some none` would both be
`null` (`Option α` as a value needs `NotNull α`, which every type that never writes `null` has).
Because a `none` field is absent, adding an `Option` field changes no existing text, and old texts
read as the new type.

## The laws

The library is organized as a [Lean Software Challenge](https://github.com/vincentqb/lean-software-challenge):
the laws are stated first, as theorems with `sorry`, and the code and the proofs follow, law by
law. Each headline states one law, independent of the others:

| headline | law | status |
|----------|-----|--------|
| `parse_render_text` | `Value.parse s = .ok v → v.render = s` | proved |
| `parse_valid` | `Value.parse s = .ok v → v.Valid` | proved |
| `render_parse` | `v.Valid → Value.parse v.render = .ok v` | not yet proved |
| `render_no_control` | every character of `v.render` is at U+0020 or above (so one line) | proved |
| `decode_text` | `decode s = .ok a → encode a = s`, for any instances | proved |
| `decode_encode` | `decode (encode a) = .ok a`, when `fromValue? (toValue a) = .ok a` and `toValue a` is valid | not yet proved |

Each has a kill, a proof that some wrong implementation fails it, and each that assumes something of
the functions it names has a witness that the assumption can hold. The two not yet proved are the
completeness directions; the tests and the Python cross-check stand for them meanwhile.

| file | who writes it | holds |
|------|---------------|-------|
| `Challenge.lean` | owner | the holes (`Value.render`, `Value.parse`, `encode`, `decode`), the headlines, kills and witnesses |
| `TomlJson/Value.lean` | owner | what the headlines are stated in: `Value`, `Value.Valid`, `ToValue`, `FromValue` |
| `TomlJson/{Float,Render,Parse,Codec}.lean` | agent | the code the holes compute through: plain, total Lean |
| `TomlJson/Printable.lean`, `TomlJson/Solution.lean` | agent | the proofs |
| `TomlJson/Main.lean` | agent | `tomljson check`, whose `main` reaches every hole |
| `TomlJson/{DateTime,Derive,Literal,LeanJson}.lean`, `TomlJson/Tests/` | agent | what the challenge does not cover |

```sh
lake build        # the library, the CLI, and the statement's checks (a kill and witness for each headline)
lake lint         # the holes' code is plain Lean and main reaches it; which headlines are proved
lake test         # the tests (examples and randomized laws run as they build)
lake comparator   # the kernel replays the proofs against Challenge.lean
```

## Lean API

* `encode`, `decode`, `encodeLines`, `decodeLines`; `ToValue`, `FromValue`, `NotNull`, and
  `deriving ToValue, FromValue` for structures and inductive types.
* `Value` (`null`, `boolean`, `integer`, `float`, `string`, `array`, `table`): `render`, `parse`,
  `renderLines`, `parseLines`, `isValid`, `get?`.
* `tomljson% { … }`: a `Value` written as JSON in Lean source, where `1` is an integer and `1.0` a
  float, `$(e)` is `toValue e`, and a repeated key is a compile error. It is Lean syntax; what it
  builds is written as ordinary JSON.
* Date-times: `LocalDate`, `LocalTime`, `LocalDateTime`, `OffsetDateTime`, `DateTime`,
  `DateTime.parse?`, `isValid`, `OffsetDateTime.now`, `ofUnixNanos?`, `toUnixNanos`.
* `Lean.Json`: `Value.toJson`, `Value.ofJson?` (a `JsonNumber` with exponent 0 is an integer, one
  with a positive exponent a float), `floatToJson`, and `open scoped TomlJson.ExactFloat`, which
  makes Lean's own `ToJson Float` (and `deriving ToJson`) exact in its scope.

Use it from another package with

```toml
[[require]]
name = "tomljson"
git = "<this repository>"
```

The library's files are `module`s, so `module` files can import them.

## What Lean does today (4.36)

`Lean.Json` keeps a number as a decimal, so it can tell `1.0` (exponent 1) from `1` (exponent 0),
but `Json.compress` prints both as `1`, `Json.parse "1.0e16"` is an integer, and `ToJson Float`
goes through `Float.toString`, six fixed decimals: `toJson 1e-7` is `0`. So no format that keeps
`1.0` apart from `1` is a fixed point of `Json.compress ∘ Json.parse`, and this library has its own
writer and reader.

Lean's TOML is Lake's (`Lake.Toml`): string, integer (`Int`, no 64-bit check), float, boolean,
date-time (offset date-time, local date-time, local date, local time), array and table. Its printer
writes floats with six decimals and `00:00:00.05` as `00:00:00.500`, and its reader rejects
`a = 6` at the very end of the input. This library does not read or write TOML.

## Tools and tests

`tomljson check < records.jsonl` exits 1 at the first line that is not canonical, with its number
and the character where it departs. [`python/tomljson.py`](python/tomljson.py) is a second writer,
in standard-library Python.

`TomlJson/Tests/` holds examples of every rule and rejection (`Examples.lean`), randomized checks
of the laws over values, their other spellings, invalid values, typed records and schema evolution
(`Properties.lean`), and compile-time errors (`DeriveErrors.lean`); they run as they build. `python3 python/crosscheck.py` checks that the Python writer and Lean
agree byte for byte on random data, and `python3 python/crosscheck.py --floats 300000` checks the
float printer against CPython's `repr` on every power of two and of ten, their neighbours and
random doubles.
