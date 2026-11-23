# lean-toml-json

Canonical JSON for TOML-typed data, with a Lean implementation. A value has exactly one text: one
line of ordinary JSON that any JSON reader reads as usual, and that Lean reads and writes back to
the same bytes (`text = render (parse text)`). Integers never have a point, floats always do,
date-times are RFC 3339 strings, and there is no `null`. The format is specified in
[`SPEC.md`](SPEC.md).

```lean
import TomlJson
open TomlJson

structure Bench where
  name : String
  iters : Nat
  time? : Option Float     -- an optional key: absent when `none`
  day : LocalDate          -- the string "2024-02-29"
  deriving ToValue, FromValue

#eval encode ({ name := "fast", iters := 100, time? := some 2.0, day := ⟨2024, 2, 29⟩ } : Bench)
-- {"day":"2024-02-29","iters":100,"name":"fast","time":2.0}

#eval (tomljson% {"name": "fast", "iters": 100, "time": 2.0, "sizes": [1, 2],
                  "day": $(LocalDate.mk 2024 2 29)}).render
-- {"day":"2024-02-29","iters":100,"name":"fast","sizes":[1,2],"time":2.0}
```

## What Lean does today (Lean 4.36)

**Lean's TOML is Lake's** (`Lake.Toml`, shipped with every toolchain). `Lake.Toml.loadToml` reads
a document into a `Lake.Toml.Table` of `Lake.Toml.Value`s:

| constructor | holds                                  | notes                                    |
|-------------|----------------------------------------|------------------------------------------|
| `string`    | `String`                               |                                          |
| `integer`   | `Int`                                  | no 64-bit check; hex, octal, binary, `_` |
| `float`     | `Float`                                | `inf`, `nan`, `-0.0` kept; exactly rounded |
| `boolean`   | `Bool`                                 |                                          |
| `dateTime`  | `Lake.Toml.DateTime`                   | below                                    |
| `array`     | `Array Value`                          | mixed types allowed                      |
| `table`     | insertion-ordered dict, `Name` keys    | dotted keys nest: `a.b = 1` is `{a = {b = 1}}` |

**Dates** are `Lake.Toml.DateTime`, TOML's four kinds: `offsetDateTime (date) (time) (offset? :
Option (Bool × Time))` (`none` is `Z`, `some (negative, hh:mm)` an offset), `localDateTime`,
`localDate` and `localTime`. A `Lake.Date` is year, month, day (`Nat`s, validated, leap years
included); a `Lake.Toml.Time` is hour, minute, second (60 allowed) and a decimal fraction as
mantissa and exponent. The reader takes `T`, `t` or a space and `Z` or `z`. They are not
connected to `Std.Time` (`PlainDate`, `PlainTime`, …), Lean's date library.

Lake's TOML *printer* (`Lake.Toml.ppTable`) loses data: floats go through `Float.toString`, six
fixed decimals (`1e-7` is written `0.000000`), and a fraction of a second with a leading zero is
written wrong (`00:00:00.05` comes back as `00:00:00.500`, because the parser stores `.05` as
mantissa 5 with exponent 1 and the printer pads to the exponent). Its reader rejects a one-digit
integer at the very end of the input (`a = 6` with no final line feed; `a = 66` is fine).

**Lean's JSON** (`Lean.Json`) keeps a number as a decimal `JsonNumber`, so it *can* tell `1.0`
(exponent 1) from `1` (exponent 0), but its printer cannot: `Json.compress` prints both as `1`.
`Json.parse "1.0e16"` is the integer `10000000000000000`, `-0.0` prints as `0`, and `1e-11` as
`0.0000000001e-1`. `ToJson Float` goes through `Float.toString` too, so `toJson 1e-7` is `0` and
`toJson 0.1234567` is `0.123457`. `Json.pretty` lists keys in the reverse of `compress`'s order.
So no format that keeps `1.0` apart from `1` is a fixed point of `Json.compress ∘ Json.parse`;
this library brings its own printer and reader.

## The format, by type

| TOML             | canonical JSON                         | Lean                        | Python (`json.loads`) |
|------------------|----------------------------------------|-----------------------------|-----------------------|
| String           | `"a\tb"` (minimal escapes, UTF-8)      | `String`                    | `str`                 |
| Integer          | `-17`, `12345678901234567890`          | `Int`, `Nat`, `UInt64`, …   | `int`                 |
| Float            | `1.0`, `0.1`, `1.0e16`, `-0.0`         | `Float`                     | `float`               |
| Float `nan`/`inf`| `"NaN"`, `"Infinity"`, `"-Infinity"`   | `Float`                     | `str` (`float(s)` reads it) |
| Boolean          | `true`                                 | `Bool`                      | `bool`                |
| Offset Date-Time | `"1979-05-27T07:32:00.5-07:00"`        | `OffsetDateTime`            | `str` (`datetime.fromisoformat`) |
| Local Date-Time  | `"1979-05-27T07:32:00"`                | `LocalDateTime`             | `str`                 |
| Local Date       | `"1979-05-27"`                         | `LocalDate`                 | `str`                 |
| Local Time       | `"07:32:00"`                           | `LocalTime`                 | `str`                 |
| Array            | `[1,"x",2.5]`                          | `Array α`, `List α`, `α × β`| `list`                |
| Table            | `{"a":1,"b":[]}` (keys sorted)         | structures, `Std.HashMap String α`, … | `dict`      |
| (absent key)     | key omitted                            | `Option α` field            | key missing           |

Floats use the shortest digits that read back (Python's `repr`, in fact, between `1e-4` and
`1e16`), always with a point: a number token is a float exactly when it contains `.`. Readers
have limits: this one takes numbers of up to 4300 digits and nesting up to 1000 deep.

## Lean API

* `Value` (`string`, `integer`, `float`, `boolean`, `array`, `table`): `render`, `parse` (any
  JSON that fits), `parseCanonical` (canonical text only), `renderLines`, `parseLines`,
  `parseLinesCanonical`, `normalize`, `mkTable`, `get?`.
* `ToValue`, `FromValue`, `deriving ToValue, FromValue`; `encode`, `decode` (lenient: an integer
  for a float, unknown keys ignored), `decodeCanonical` (the text must be the canonical encoding,
  so `decodeCanonical s = .ok a → encode a = s`), and the `…Lines` versions.
* `tomljson% { … }`: a `Value` written as JSON in Lean source; `1` is an integer, `1.0` a float,
  `$(e)` is `toValue e`.
* Date-times: `LocalDate`, `LocalTime`, `LocalDateTime`, `OffsetDateTime`, `DateTime`,
  `DateTime.parse?`, `isValid`, `OffsetDateTime.now`, `ofUnixNanos?`, `toUnixNanos`.
* `Lean.Json`: `Value.toJson`, `Value.ofJson?` (a `JsonNumber` with exponent 0 is an integer, one
  with a positive exponent a float), `floatToJson`, and `open scoped TomlJson.ExactFloat`, which
  makes Lean's own `ToJson Float` (and `deriving ToJson`) exact in its scope.
* `TomlJsonLake` (a separate library, since importing Lake links all of it): `ofTomlText`,
  `Value.ofToml`, `Value.toToml`, `DateTime.ofLake`, `DateTime.toLake`.

Use it from another package with

```toml
[[require]]
name = "tomljson"
git = "<this repository>"
```

The library's files are `module`s, so `module` files can import them.

## Other tools

Reading needs nothing: `json.loads`, `JSON.parse`, `jq` read canonical lines as usual. Writing
canonical lines needs the shortest-float layout, sorted keys and the extra escapes:
[`python/tomljson.py`](python/tomljson.py) does it (`dumps`), and `tomljson canon` canonicalizes
any JSON Lines:

```
lake build tomljson
.lake/build/bin/tomljson canon < any.jsonl > canonical.jsonl
.lake/build/bin/tomljson check < canonical.jsonl
```

## Tests

`lake test` builds `Tests/`, whose checks run as it builds: examples of every rule
(`Tests/Examples.lean`), randomized laws over values, their non-canonical spellings, typed records
and date-times (`Tests/Properties.lean`), and Lake's TOML values (`Tests/Lake.lean`).
`python3 python/crosscheck.py` checks that the Lean CLI and the Python encoder agree byte for byte
on random data and that `json.loads` reads integers and floats apart;
`python3 python/crosscheck.py --floats 300000` checks the float printer against CPython's `repr`
on every power of two and of ten, their neighbours and random doubles.
