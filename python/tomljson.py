"""Canonical TOML-JSON in Python, standard library only.

Reading needs nothing special: canonical text is JSON, and ``json.loads`` reads it as usual
(integers as ``int``, floats as ``float``). ``loads`` here adds the format's rules on input, as
the Lean reader has them: no ``NaN``/``Infinity`` literals, no float beyond binary64's range, no
number of more than 4300 digits, no duplicate keys, no unpaired surrogate, ``null`` only as a
member (then dropped).

Writing canonical text needs ``dumps``: ``json.dumps`` would write ``1e-07`` (no point), keep
U+0085 and U+2028 raw (which ``str.splitlines`` splits on) and not sort keys. ``dumps(json.loads(
line)) == line`` for every canonical line, byte for byte, within CPython's limits (integers of at
most 4300 digits, nesting within the recursion limit).
"""

import json
import math

__all__ = ["dumps", "loads", "dumps_float"]

# The most digits a number may have, as CPython's own limit on int text and the Lean reader's.
MAX_NUMBER_DIGITS = 4300

# Characters JSON lets through raw that the format escapes: DEL, the C1 controls, and the line
# and paragraph separators. (json.dumps already escapes U+0000-U+001F, '"' and '\\'.)
_EXTRA_ESCAPES = {c: "\\u%04x" % c for c in [*range(0x7F, 0xA0), 0x2028, 0x2029]}


def dumps_float(x: float) -> str:
    """The canonical text of a float: shortest round-trip digits, always with a point."""
    if math.isnan(x):
        return '"NaN"'
    if math.isinf(x):
        return '"Infinity"' if x > 0 else '"-Infinity"'
    r = repr(x)  # shortest round-trip digits; fixed notation for exponents in [-4, 16)
    if "e" not in r:
        return r
    mantissa, exponent = r.split("e")
    if "." not in mantissa:
        mantissa += ".0"
    return f"{mantissa}e{int(exponent)}"


def _string(s: str) -> str:
    text = json.dumps(s, ensure_ascii=False)
    try:
        text.encode("utf-8")
    except UnicodeEncodeError:
        raise ValueError("a string holds an unpaired surrogate") from None
    return text.translate(_EXTRA_ESCAPES)


def _dump(v, out: list) -> None:
    if isinstance(v, bool):
        out.append("true" if v else "false")
    elif isinstance(v, int):
        out.append(str(v))
    elif isinstance(v, float):
        out.append(dumps_float(v))
    elif isinstance(v, str):
        out.append(_string(v))
    elif isinstance(v, (list, tuple)):
        out.append("[")
        for i, item in enumerate(v):
            if i:
                out.append(",")
            if item is None:
                raise ValueError("None has no TOML counterpart (only a member may be None: it is dropped)")
            _dump(item, out)
        out.append("]")
    elif isinstance(v, dict):
        out.append("{")
        first = True
        for key in sorted(v):  # code point order, as Lean's String order
            if not isinstance(key, str):
                raise TypeError(f"table keys are strings, not {type(key).__name__}")
            if v[key] is None:
                continue
            if not first:
                out.append(",")
            first = False
            out.append(_string(key))
            out.append(":")
            _dump(v[key], out)
        out.append("}")
    elif v is None:
        raise ValueError("None has no TOML counterpart")
    else:
        raise TypeError(f"no canonical JSON for {type(v).__name__}")


def dumps(v) -> str:
    """The canonical text of ``v`` (one line, without its line feed)."""
    out: list = []
    _dump(v, out)
    return "".join(out)


def _pairs(pairs):
    table = {}
    for key, value in pairs:
        if key in table:
            raise ValueError(f"duplicate key {key!r}")
        table[key] = value
    return {k: v for k, v in table.items() if v is not None}


def _constant(name):
    raise ValueError(f"{name} is not JSON")


def _float(token: str) -> float:
    significand = token.lower().split("e")[0]
    if sum(c.isdigit() for c in significand) > MAX_NUMBER_DIGITS:
        raise ValueError(f"a number has more than {MAX_NUMBER_DIGITS} digits")
    x = float(token)
    if math.isinf(x):
        raise ValueError(f"{token} is beyond the range of binary64")
    return x


def _check(v):
    """Reject null outside a member, and unpaired surrogates (a Lean string has none)."""
    if v is None:
        raise ValueError("null has no TOML counterpart")
    if isinstance(v, str):
        if any(0xD800 <= ord(c) <= 0xDFFF for c in v):
            raise ValueError("unpaired surrogate")
    elif isinstance(v, list):
        for item in v:
            _check(item)
    elif isinstance(v, dict):
        for key, item in v.items():
            _check(key)
            _check(item)
    return v


def loads(text: str):
    """The value of a JSON text under the format's rules (see the module docstring)."""
    return _check(
        json.loads(text, object_pairs_hook=_pairs, parse_constant=_constant, parse_float=_float))
