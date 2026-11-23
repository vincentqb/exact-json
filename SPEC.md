# Canonical TOML-JSON

A subset of JSON for TOML-typed data. Version 0.1.

A canonical text is one line of ordinary JSON (RFC 8259): any JSON reader reads it as usual, and a
file of them is ordinary JSON Lines. What makes it canonical is that each value has exactly one
text, so a reader that knows the format can read a text and write it back to the same bytes:

```
text = render (parse text)        for every canonical text
```

and `parse (render v) = v` for every value `v` in normal form. The data model is TOML's: an
integer is never confused with a float, and a date-time is a string in its RFC 3339 form.

The reference implementation is the Lean library in this repository (`TomlJson`); `python/tomljson.py`
is a second one, in about a hundred lines of standard-library Python, and the two agree byte for
byte (`python/crosscheck.py`).

## 1. Data model

A value is one of:

| type    | domain                                                   | TOML       |
|---------|----------------------------------------------------------|------------|
| string  | a sequence of Unicode scalar values (no lone surrogates) | String     |
| integer | an integer, without bound                                | Integer    |
| float   | a finite IEEE 754 binary64 number (`-0.0` included)      | Float      |
| boolean | `true` or `false`                                        | Boolean    |
| array   | a sequence of values, of any types                       | Array      |
| table   | a map from strings to values, keys unique                | Table      |

There is no null: an absent table key is how a missing value is written, as in TOML.

TOML's date-time types and the non-finite floats have no JSON number or literal, so they are
strings by convention (section 4); a reader that knows the field's type reads them back.

TOML asks for integers of at least 64 bits; the format has no bound (nor does Lean's `Int`, nor
Lake's TOML reader). Readers with fixed-width integers lose values beyond their range:
JavaScript beyond ±(2⁵³ − 1), 64-bit readers beyond the 64-bit range.

Readers do have limits, and so does this one: it reads numbers of at most 4300 digits (CPython's
own limit on `int` text) and nesting at most 1000 deep. The laws of section 3 are about values
within these limits.

## 2. Canonical text

A canonical text has no whitespace outside strings. In ABNF (RFC 5234), with `float` and the
order of table members as defined below:

```abnf
value     = string / integer / float / %s"true" / %s"false" / array / table
array     = "[" [ value *( "," value ) ] "]"
table     = "{" [ member *( "," member ) ] "}"
member    = string ":" value
integer   = "0" / [ "-" ] %x31-39 *%x30-39
string    = %x22 *( unescaped / escape ) %x22
escape    = "\" ( %x22 / "\" / "b" / "t" / "n" / "f" / "r" / "u" 4hexlower )
hexlower  = %x30-39 / %x61-66
unescaped = <any Unicode scalar value but those escaped below>
```

**Integers** have no point and no exponent, no leading zero, no `+`, and no `-0`.

**Floats** always have a point. For a finite `x`:

* zero is `0.0`, negative zero `-0.0`;
* otherwise, take the *shortest* digits `d₁d₂…dₙ` (`d₁ ≠ 0`, `dₙ ≠ 0`) and exponent `E` such that
  `d₁.d₂…dₙ × 10^E` reads back as `x` (rounding to nearest, ties to even); among several shortest,
  the one nearest `x`, and of two equally near, the one ending in an even digit. Then write
  `-` if `x` is negative, and
  * if `-4 ≤ E < 16`, fixed notation with at least one digit after the point:
    `123.456`, `1.0`, `1000000000000000.0`, `0.0001`;
  * otherwise `d₁`, `.`, `d₂…dₙ` (or `0` if `n = 1`), `e`, `E` in decimal with `-` if negative and
    no `+` or leading zero: `1.0e16`, `1.5e-7`, `5.0e-324`, `1.7976931348623157e308`.

  These are the digits of Python's `repr`, JavaScript's `Number.prototype.toString` and Ryu; in the
  fixed range the text is exactly Python's `repr`. Outside it, Python writes `1e-05` where this
  format writes `1.0e-5`.

So a number token is a float exactly when it contains `.`, and an integer otherwise.

**Strings** escape exactly these characters, and no others:

| character                                   | escape              |
|---------------------------------------------|---------------------|
| `"` and `\`                                 | `\"`, `\\`          |
| U+0008, U+0009, U+000A, U+000C, U+000D      | `\b`, `\t`, `\n`, `\f`, `\r` |
| other U+0000–U+001F, U+007F–U+009F (all Cc) | `\u00xx`, lower-case hex |
| U+2028, U+2029                              | `\u2028`, `\u2029`  |

Every other character is written as itself, in UTF-8: no `\/`, no `\u` for printable characters,
no surrogate pairs. This is JSON's own minimal escaping (as RFC 8785 and Python's
`json.dumps(ensure_ascii=False)` do it) plus the C1 controls, DEL and the two separators, so that a
canonical line holds no control character and nothing any line splitter breaks on (Python's
`str.splitlines` splits at U+0085, U+2028 and U+2029). The escaped string is also a valid TOML
basic string.

**Tables** list their members with keys strictly increasing in code point order, which is UTF-8
byte order and the order of Lean's and Python's string comparison. (RFC 8785 sorts by UTF-16
code units instead; the two differ only on keys with characters above U+FFFF.)

**JSON Lines.** A canonical JSON Lines text is a sequence of canonical texts, each followed by one
line feed (U+000A): no carriage return, no blank line, no byte order mark. The empty text holds no
values.

## 3. Laws

For the reference implementation (`Value.render`, `Value.parse`, `Value.parseCanonical`,
`encode`, `decode`, `decodeCanonical`), and values within the reader's limits (integers of at most
4300 digits, nesting at most 1000 deep; a constructor with named arguments nests two levels):

1. Every canonical text is a JSON text and a single line.
2. `parse (render v) = normalize v` for every value, and `render` is injective on normal values,
   so canonical texts and normal values are in bijection. (`normalize` sorts tables, keeps the last
   of repeated keys, and writes non-finite floats as their names.)
3. `parseCanonical s` succeeds exactly when `s` is canonical, and then `render (parseCanonical s) = s`.
4. For a type with `ToValue` and `FromValue` instances (derived or the library's),
   `decodeCanonical (encode a) = a`, and `decodeCanonical s = a` implies `encode a = s`. Floats
   come back up to a NaN's payload, and `Value` itself up to `normalize`. Date-times must be valid
   (`isValid`: a real date, fields in range); an invalid one is written as text no reader accepts.
   Field names must give distinct keys (`x` and `x?` do not), which deriving checks.

These are checked, not proved: by compile-time examples, by randomized tests over values, their
non-canonical spellings and typed records (`Tests/`), by every power of two and of ten, their
neighbours and random doubles against CPython's `repr` (`python/crosscheck.py --floats`), and by
byte-for-byte agreement with the Python implementation on random data.

## 4. Typed conventions

A reader that knows a field's type reads these strings back as typed values; any other reader sees
strings.

**Date-times** are RFC 3339 strings in TOML's four types:

| TOML             | canonical text                                             |
|------------------|------------------------------------------------------------|
| Offset Date-Time | `1979-05-27T07:32:00Z`, `1979-05-27T00:32:00.999999-07:00` |
| Local Date-Time  | `1979-05-27T07:32:00`                                      |
| Local Date       | `1979-05-27`                                               |
| Local Time       | `07:32:00`, `00:32:00.5`                                   |

with an upper-case `T`, the seconds always written, a fraction only when nonzero and without
trailing zeros (at most nine digits: nanoseconds), and a zero offset as `Z` (any other as
`±HH:MM`). Years are 0000 to 9999; second 60 is a leap second, as RFC 3339 allows (Python's
`datetime` refuses it).

**Non-finite floats** are the strings `"NaN"`, `"Infinity"` and `"-Infinity"`, the spellings that
Lean's `FromJson Float`, JavaScript's `Number` and Python's `float` read as such.

**Optional fields** are absent keys, never `null`.

**Structures and sum types** (`deriving ToValue, FromValue`) have the shapes of Lean's
`deriving ToJson`: a structure is a table of its fields (a field `x?` under the key `x`); a
constructor without arguments is its name, `"red"`; one with named arguments is
`{"circle":{"radius":1.0}}`; one unnamed argument, `{"some":3}`; several, `{"pair":[1,"x"]}`.
Two differences, both for TOML's lack of null: a field or named argument of type `Option α` is
omitted when `none` (Lean writes `null`), and a named argument `x?` is written under `x`, as a
field is (Lean keeps `x?`).

## 5. Reading other JSON

`parse` (and `decode`) read any JSON text whose data fits the model:

* whitespace, any member order, any escape (`\/`, surrogate pairs, either case of hex digits);
* any number spelling: without a point or exponent an integer, otherwise the nearest float
  (`1E5` is the float `100000.0`, `-0` the integer `0`);
* a member whose value is `null` is dropped (an absent key); `null` anywhere else is an error;
* typed reading also takes an integer where a float is expected (JavaScript writes `1.0` as `1`),
  ignores unknown keys in a structure's table (a constructor's table has exactly one key, its
  name), and reads a date-time in any form TOML allows (`t` or a space for `T`, `z`, `+00:00`, no
  seconds, a longer fraction, truncated);
* JSON Lines may end lines with CR LF and have blank lines (JSON whitespace only), which are
  skipped.

They reject: duplicate keys, unpaired surrogates, raw U+0000–U+001F in strings, floats beyond
binary64's range (`1e400`), numbers of more than 4300 digits (CPython's limit for `int`; an
exponent's digits do not count), nesting deeper than 1000, `NaN` and `Infinity` literals, and
trailing text.

`parseCanonical` and `decodeCanonical` accept only canonical text and, for `decodeCanonical`, the
canonical encoding of a value of the type (no ignored key, no integer for a float).

Re-serializing with other tools does not, in general, keep the canonical form (JavaScript writes
`1.0` as `1`, jq writes `1.0e16` as `1.0E+16`); `tomljson canon` or `python/tomljson.py`'s `dumps`
restores it.

## 6. Why not an existing format

* **`Lean.Json.compress ∘ Lean.Json.parse`** (Lean 4.36) maps `1.0` to `1`, so no format that keeps
  integral floats apart from integers is its fixed point; it also maps `1.0e16` to the integer
  `10000000000000000`, `-0.0` to `0` and `1e-11` to `0.0000000001e-1`. Lean's `ToJson Float` goes
  through `Float.toString`, six fixed decimals, so `toJson 1e-7` is `0` and `toJson 0.1234567` is
  `0.123457`. `Json.pretty` lists keys in the reverse of `compress`'s order.
* **RFC 8785 (JCS)** is canonical JSON, but its numbers are JavaScript's: `1.0` is `1`, so the
  integer/float distinction is lost.
* **`json.dumps(sort_keys=True, separators=(",", ":"), ensure_ascii=False)`** is close, but writes
  `1e-07` (no point) and keeps U+0085, U+2028 and U+2029 raw.
* **toml-test's JSON encoding** tags every scalar (`{"type": "integer", "value": "1"}`): exact, but
  not data that other software reads as usual.
