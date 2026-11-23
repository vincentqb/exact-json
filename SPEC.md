# Canonical, strictly typed JSON

Version 0.2. One line of ordinary JSON per value, which any JSON reader parses, and which Lean
writes and reads back under one law. For a Lean type `α` with `ToValue` and `FromValue`
instances (derived or the library's):

```
decode s = .ok a   ↔   encode a = s
```

for every valid `a` (section 2) within the reader's limits (section 5), with `a` compared by what
it means: floats up to a NaN's payload, maps (`Std.TreeMap`, `Std.HashMap`) by their entries
rather than their internal layout. So:

* reading undoes writing: `decode (encode a) = a`;
* each value has one text, and `encode (decode s) = s` whenever `decode s` succeeds;
* nothing else is read: no other spelling of the same data, no other type's data.

The integer/float split and the date-time types follow TOML's data model; nothing else in the
format depends on TOML. The reference implementation is the Lean library in this repository;
`python/tomljson.py` is a second writer, used as an oracle in the tests.

## 1. Untyped values

Text and Lean types meet in `Value`:

| constructor | holds                                                           |
|-------------|-----------------------------------------------------------------|
| `null`      |                                                                 |
| `boolean`   | `Bool`                                                          |
| `integer`   | `Int`, without bound                                            |
| `float`     | `Float` (IEEE 754 binary64)                                     |
| `string`    | `String` (Unicode scalar values)                                |
| `array`     | an array of values                                              |
| `table`     | an array of key-value pairs                                     |

`Value` obeys the law too (`Value.parse`, `Value.render`), with `parse s = .ok v ↔ (v valid ∧
render v = s)`.

## 2. Validity

A value is valid when every float is finite and every table's keys strictly increase in code point
order (Lean's `String` order, which is UTF-8 byte order). Exactly the valid values have canonical
texts. `render` writes any value as it is: an invalid one gets a text that the reader rejects (a
table out of order as it stands, a non-finite float as the bare token `NaN`, `Infinity` or
`-Infinity`, which is not JSON), never another value's text.

Date-times have their own validity (`isValid`: a real calendar date and time, fields in range);
an invalid one is written as a string the reader rejects.

Encodings the library derives or defines produce valid values only.

## 3. Canonical text

No whitespace outside strings. In ABNF (RFC 5234), with `float` and the order of table members as
below:

```abnf
value     = %s"null" / %s"true" / %s"false" / integer / float / string / array / table
array     = "[" [ value *( "," value ) ] "]"
table     = "{" [ member *( "," member ) ] "}"          ; keys strictly increasing
member    = string ":" value
integer   = "0" / [ "-" ] %x31-39 *%x30-39
string    = %x22 *( unescaped / escape ) %x22
escape    = "\" ( %x22 / "\" / "b" / "t" / "n" / "f" / "r" / "u00" 2hexlower )
hexlower  = %x30-39 / %x61-66
unescaped = <any Unicode scalar value but ", \ and U+0000-U+001F>
```

**Integers** have no point and no exponent, no leading zero, no `+`, and no `-0`.

**Floats** always have a point. For a finite `x`:

* zero is `0.0`, negative zero `-0.0`;
* otherwise take the *shortest* digits `d₁d₂…dₙ` (`d₁ ≠ 0`, `dₙ ≠ 0`) and exponent `E` such that
  `d₁.d₂…dₙ × 10^E` reads back as `x` (rounding to nearest, ties to even); among several shortest,
  the one nearest `x`, and of two equally near, the one ending in an even digit. Write `-` if `x`
  is negative, then
  * if `-4 ≤ E < 16`, fixed notation with at least one digit after the point: `123.456`, `1.0`,
    `1000000000000000.0`, `0.0001`;
  * otherwise `d₁`, `.`, `d₂…dₙ` (or `0` if `n = 1`), `e`, then `E` in decimal, with `-` if
    negative and no `+` or leading zero: `1.0e16`, `1.5e-7`, `5.0e-324`, `1.7976931348623157e308`.

These are the digits of Python's `repr`, JavaScript's `Number.prototype.toString` and Ryu; in the
fixed range the text is exactly Python's `repr`. A number token is a float exactly when it
contains `.`.

**Strings** use JSON's minimal escaping, as RFC 8785 and Python's
`json.dumps(ensure_ascii=False)` do: `\"` and `\\`; `\b`, `\t`, `\n`, `\f`, `\r` for U+0008,
U+0009, U+000A, U+000C, U+000D; `\u00xx` (lowercase hex) for the other characters below U+0020.
Every other character is written as itself, in UTF-8: no `\/`, no `\u` for any other character,
no surrogate pairs.

**Tables** list their members with keys strictly increasing in code point order. (RFC 8785 sorts by
UTF-16 code units instead; the two differ only on keys with characters above U+FFFF.)

**JSON Lines.** A canonical JSON Lines text is a sequence of canonical texts, each followed by one
line feed (U+000A): no carriage return, no blank line, no byte order mark. The empty text holds no
values.

## 4. Typed encodings

**`none`** is an absent key when it is a structure field (or a named constructor argument), and
`null` anywhere else:

| Lean                                   | written as                                   |
|----------------------------------------|----------------------------------------------|
| field `x : Option α`                   | key absent for `none`, `"x":…` for `some a`  |
| field `x : Option (Option α)`          | absent, `"x":null`, or `"x":…`               |
| `Array (Option α)`, top level, …       | `null` for `none`: `[1,null,3]`              |

`Option α` as a value needs `NotNull α` (`α` never writes `null`): otherwise `none` and `some none`
would have one text. The library's types and every derived type have it; `Option α` and `Value`
do not. The field rule holds for a field whose type is a type parameter too (`Box (Option Nat)`
writes `{}` for a `none` field); a derived type applied to `Option (Option α)` is refused, since its
instance also asks the parameter for `ToValue`. Because a `none` field is absent, adding an
`Option` field to a type changes no existing text, and old texts read as the new type with `none`
there.

**Floats** that are not finite are the strings `"NaN"`, `"Infinity"` and `"-Infinity"`, which
`decode` reads back as floats.

**Date-times** are strings in one canonical RFC 3339 form each:

| kind (Lean type)                    | canonical text                                             |
|-------------------------------------|------------------------------------------------------------|
| offset date-time (`OffsetDateTime`) | `1979-05-27T07:32:00Z`, `1979-05-27T00:32:00.999999-07:00` |
| local date-time (`LocalDateTime`)   | `1979-05-27T07:32:00`                                      |
| date (`LocalDate`)                  | `1979-05-27`                                               |
| time of day (`LocalTime`)           | `07:32:00`, `00:32:00.5`                                   |

An upper-case `T`; seconds always written; a fraction only when nonzero, without trailing zeros, at
most nine digits; a zero offset as `Z`, any other as `±HH:MM`. Years are 0000 to 9999. Second 60
is accepted at any time, for a leap second; whether one occurred then is not checked.

**Structures and sum types** (`deriving ToValue, FromValue`) have the shapes of Lean's
`deriving ToJson`: a structure is a table of its fields (a field `x?` under the key `x`); a
constructor without arguments is its name, `"red"`; one with named arguments is
`{"circle":{"radius":1.0}}`, those arguments following the rules of fields; one unnamed argument,
`{"some":3}`; several, `{"pair":[1,"x"]}`. Unlike Lean's, a `none` field or named argument is absent
rather than `null`, and a named argument `x?` is written under `x` as a field is. Keys must differ
(fields `x` and `x?` do not), which deriving checks.

**Other types:** `Nat`, `Int` and the fixed-width integers are integers (read only in range);
`Char` is a one-character string; `Array α` and `List α` are arrays; `α × β` is a two-item array;
`Std.TreeMap String α` and `Std.HashMap String α` are tables.

## 5. Reading

Reading takes canonical text and nothing else. These are errors, each at its byte offset, naming
the canonical spelling where there is one: whitespace; any number spelling but the canonical one
(`1e5` for `100000.0`, `1.50`, `-0` for `0`, `01` for `1`); any escape but the canonical ones
(`\/`, `\u0041` for `A`, `\u000a` for `\n`, upper-case hex, surrogate pairs); raw U+0000–U+001F in
strings; keys out of order or repeated; floats beyond binary64's range; trailing text. In JSON
Lines, the first line that is not canonical is reported, with its number.

Typed reading is strict as well: no integer where a float belongs, no key a type does not have, no
missing key for a field that is not an `Option`, no `null` where the type has none, no date-time
in any form but its canonical one.

Limits, which bound the reader's work: at most 4300 digits in a number (CPython's limit for `int`
text) and nesting at most 1000 deep (a constructor with named arguments nests two levels). The law
holds for values within them.

## 6. Why not `Lean.Json`

`Lean.Json.compress ∘ Lean.Json.parse` (Lean 4.36) maps `1.0` to `1`, so no format that keeps
integral floats apart from integers is its fixed point; it also maps `1.0e16` to the integer
`10000000000000000`, `-0.0` to `0` and `1e-11` to `0.0000000001e-1`. Lean's `ToJson Float` goes
through `Float.toString`, six fixed decimals, so `toJson 1e-7` is `0` and `toJson 0.1234567` is
`0.123457`. `Json.pretty` lists keys in the reverse of `compress`'s order.

## 7. Checking

The law is checked, not proved: by compile-time examples of every rule and of every rejection; by
randomized tests over valid values, their non-canonical spellings (all rejected), invalid values
(never read as another value), typed records and schema evolution (`Tests/`); by every power of
two and of ten, their neighbours and random doubles against CPython's `repr`
(`python/crosscheck.py --floats`); and by byte-for-byte agreement with the Python writer on random
data (`python/crosscheck.py`).
