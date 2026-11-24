r"""Canonical JSON in Python, standard library only: a second implementation of the writer.

Canonical text is JSON, and ``json.loads`` reads it as usual. ``dumps`` writes it, byte for byte
as the Lean library does: no whitespace, keys in code point order, integers without a point,
floats with the shortest digits that read back and always a point, JSON's escapes for ``"``, ``\``
and the C0 controls plus ``\uXXXX`` for DEL, the C1 controls and U+2028/U+2029, and ``None`` as
``null``. The test suite uses it as an independent oracle (CPython's ``repr`` gives
the float digits).
"""

import json
import math

__all__ = ["dumps", "dumps_float"]


def dumps_float(x: float) -> str:
    """The canonical text of a finite float: shortest round-trip digits, always with a point."""
    if not math.isfinite(x):
        raise ValueError(f"{x} has no JSON text")
    # float.__repr__, not repr: a subclass (numpy's float64) may print otherwise, as json does
    r = float.__repr__(x)  # shortest round-trip digits; fixed notation for exponents in [-4, 16)
    if "e" not in r:
        return r
    mantissa, exponent = r.split("e")
    if "." not in mantissa:
        mantissa += ".0"
    return f"{mantissa}e{int(exponent)}"


_ESCAPED = {c: f"\\u{c:04x}" for c in [*range(0x7F, 0xA0), 0x2028, 0x2029]}


def _string(s: str) -> str:
    text = json.dumps(s, ensure_ascii=False).translate(_ESCAPED)
    try:
        text.encode("utf-8")
    except UnicodeEncodeError:
        raise ValueError("a string holds an unpaired surrogate") from None
    return text


def _dump(v, out: list) -> None:
    if v is None:
        out.append("null")
    elif isinstance(v, bool):
        out.append("true" if v else "false")
    elif isinstance(v, int):
        out.append(int.__repr__(v))
    elif isinstance(v, float):
        out.append(dumps_float(v))
    elif isinstance(v, str):
        out.append(_string(v))
    elif isinstance(v, (list, tuple)):
        out.append("[")
        for i, item in enumerate(v):
            if i:
                out.append(",")
            _dump(item, out)
        out.append("]")
    elif isinstance(v, dict):
        out.append("{")
        for i, key in enumerate(sorted(v)):  # code point order, as Lean's String order
            if not isinstance(key, str):
                raise TypeError(f"table keys are strings, not {type(key).__name__}")
            if i:
                out.append(",")
            out.append(_string(key))
            out.append(":")
            _dump(v[key], out)
        out.append("}")
    else:
        raise TypeError(f"no canonical JSON for {type(v).__name__}")


def dumps(v) -> str:
    """The canonical text of ``v`` (one line, without its line feed)."""
    out: list = []
    _dump(v, out)
    return "".join(out)
