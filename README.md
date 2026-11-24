# ExactJSON

Exact JSON: canonical, strictly typed JSON for Lean. A value is written as one line of ordinary
JSON, which any JSON reader parses, and Lean reads it back under one law:

```
decode s = .ok a   ↔   encode a = s
```

Reading undoes writing, each value has exactly one text, and no other text is read: no
whitespace, no other number spelling, no integer for a float, no unknown key. Integers never have
a point and floats always do, `none` is an absent key as a field and `null` elsewhere, date-times
are RFC 3339 strings. The format is specified in [`SPEC.md`](SPEC.md), and its laws are stated
as theorems in [`Challenge.lean`](Challenge.lean) (see [The laws](#the-laws)).

```lean
import ExactJSON
open ExactJSON

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
| `parse_fixed` | `Value.parse s = .ok v ↔ Rfc8259.read? s = some v ∧ v.render = s` | proved |
| `read_render` | `v.Valid → Rfc8259.read? v.render = some v` | not yet proved |
| `readJson_spec` | `(Value.readJson s).toOption = Rfc8259.read? s` | proved |
| `parse_costed` | `(Value.parseCosted s).value = Value.parse s` | proved |
| `parse_linear` | `∃ c, ∀ s, (Value.parseCosted s).steps ≤ c * (s.length + 1)` | proved, with `c = 22` |
| `render_no_control` | every character of `v.render` is at U+0020 or above (so no line feed or carriage return) | proved |
| `decode_text` | `decode s = .ok a → encode a = s`, for any instances | proved |
| `decode_encode` | `decode (encode a) = .ok a`, when `fromValue? (toValue a) = .ok a` and `toValue a` is valid | not yet proved |

Each has a kill, a proof that some wrong implementation fails it, and each that assumes something of
the functions it names has a witness that the assumption can hold.

`Rfc8259.read?` is part of the statement: RFC 8259's grammar, written to be checked against the
RFC, and what a JSON text holds (an integer when a number has no fraction and no exponent, the
nearest float otherwise; no repeated key; no lone surrogate). `parse_fixed` says the canonical
texts are exactly the JSON texts that reading and writing back leaves unchanged, so the format is
a consistent subset of JSON, and `canon s := render <$> readJson s` brings any JSON text to its
canonical form. The two headlines not yet proved both follow from one lemma about floats, that
every finite float's canonical text reads back as it (`FloatsReadBack` in `ExactJSON/Fixed.lean`,
with `read_render_of_floats` and `decode_encode_of_floats`); the tests and the Python
cross-checks stand for it meanwhile.

Because the soundness laws are proved, the code does no defensive work: `Value.parse` does not
check what it read (by rendering it again, or validating it), and `decode` compares the value it
read with the one its result is written as, instead of encoding it again. `parse_linear` bounds
the steps as `Value.parseCosted` counts them, which the reader charges itself: a step for each
byte decoded, each character it examines (in the text, or in a text compared with it) and each
character counted to place an error. So it bounds the reader's own count, not its running time;
the arithmetic on numbers and the wording of error messages are not counted.

| file | who writes it | holds |
|------|---------------|-------|
| `Challenge.lean` | owner | the holes (`Value.render`, `Value.parse`, `Value.parseCosted`, `Value.readJson`, `encode`, `decode`), the headlines, kills and witnesses |
| `ExactJSON/Value.lean`, `ExactJSON/Rfc8259.lean` | owner | what the headlines are stated in: `Value`, `Value.Valid`, `ToValue`, `FromValue`, `Costed`, and the RFC 8259 reference reader `Rfc8259.read?` |
| `ExactJSON/{Float,Render,Parse,Codec}.lean` | agent | the code the holes compute through: plain, total Lean |
| `ExactJSON/{Text,Printable,NumberValid,NumberText,Reread,Sound,Cost,SpecValid,Fixed,Solution}.lean` | agent | the proofs: the renderer's text, no character below U+0020, the reader's soundness, its steps, what RFC 8259 reads in a canonical text, the fixed points |
| `ExactJSON/Main.lean` | agent | `exactjson check` and `exactjson canon`, whose `main` reaches every hole |
| `ExactJSON/{DateTime,Derive,Literal,LeanJson}.lean`, `ExactJSON/Tests/` | agent | what the challenge does not cover |

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
  `renderLines`, `parseLines`, `isValid`, `get?`; `readJson` for JSON in any spelling (RFC 8259,
  as `Rfc8259.read?` reads it), whose result `render` writes canonically.
* `exactjson% { … }`: a `Value` written as JSON in Lean source, where `1` is an integer and `1.0` a
  float, `$(e)` is `toValue e`, and a repeated key is a compile error. It is Lean syntax; what it
  builds is written as ordinary JSON.
* Date-times: `LocalDate`, `LocalTime`, `LocalDateTime`, `OffsetDateTime`, `DateTime`,
  `DateTime.parse?`, `isValid`, `OffsetDateTime.now`, `ofUnixNanos?`, `toUnixNanos`.
* `Lean.Json`: `Value.toJson`, `Value.ofJson?` (a `JsonNumber` with exponent 0 is an integer, one
  with a positive exponent a float), `floatToJson`, and `open scoped ExactJSON.ExactFloat`, which
  makes Lean's own `ToJson Float` (and `deriving ToJson`) exact in its scope.

Use it from another package with

```toml
[[require]]
name = "exactjson"
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

`exactjson check < records.jsonl` exits 1 at the first line that is not canonical, with its number
and the character where it departs. `exactjson canon < any.json` writes the canonical text of a JSON
text in any spelling (`--lines` for one text a line), and exits 1, saying why and where, at one
that RFC 8259 does not read or that holds what a value cannot (a repeated key, a lone surrogate, a
float beyond binary64). [`python/exactjson.py`](python/exactjson.py) is a second writer, in
standard-library Python.

`ExactJSON/Tests/` holds examples of every rule and rejection (`Examples.lean`), randomized checks
of the laws over values, their other spellings, invalid values, typed records and schema evolution
(`Properties.lean`), and compile-time errors (`DeriveErrors.lean`); they run as they build. `python3 python/crosscheck.py` checks that the Python writer and Lean
agree byte for byte on random data, and that `exactjson canon` reads Python's `json.dumps` of it
(spaces, ASCII escapes, keys in any order) as the same values, and `python3 python/crosscheck.py --floats 300000` checks the
float printer against CPython's `repr` on every power of two and of ten, their neighbours and
random doubles.
