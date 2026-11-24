"""Cross-check the Lean reader against an independent Python writer.

    lake build exactjson && python3 python/crosscheck.py [--count N] [--seed S]
    python3 python/crosscheck.py --floats N

1. Random Python values, written by ``exactjson.dumps``, are canonical to ``exactjson check``, which
   accepts a line only if it is exactly how Lean writes that value: so the two writers agree byte
   for byte.
2. ``json.loads`` reads every such line back as the same value, with integers from tokens without
   a point and floats from tokens with one.
3. Other spellings of the same values (``json.dumps``'s spaces and ASCII escapes) are rejected.
4. ``exactjson canon`` reads any JSON spelling of them (``json.dumps`` with spaces, ASCII escapes
   and keys in any order) and writes each one's canonical text, byte for byte as Python's writer.

With ``--floats N``: every power of two and of ten, their neighbours, the smallest subnormals and N
random doubles, written with CPython's ``repr`` digits, are canonical to Lean.
"""

import argparse
import json
import math
import random
import struct
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from exactjson import dumps, dumps_float  # noqa: E402

EXE = Path(__file__).resolve().parent.parent / ".lake" / "build" / "bin" / "exactjson"

SPECIAL = ['"', "\\", "/", "\n", "\t", "\r", "\b", "\f", "\x00", "\x1f", "\x7f", "\x85", "\x9f",
           "\xa0", "\u2028", "\u2029", "\ufeff", "\uffff", "\U00010000", "\U0010ffff", "\u00e9", "\u4e2d",
           "\U0001f600"]


def rand_char(r):
    k = r.randrange(6)
    if k == 0:
        return chr(r.randrange(0x20, 0x7F))
    if k == 1:
        return r.choice(SPECIAL)
    if k == 2:
        return chr(r.randrange(0xA0, 0xD800))
    if k == 3:
        return chr(r.randrange(0xE000, 0x10000))
    if k == 4:
        return chr(r.randrange(0x10000, 0x110000))
    return chr(r.randrange(0x61, 0x7B))


def rand_float(r):
    k = r.randrange(4)
    if k == 0:
        return r.choice([0.0, -0.0, 1.0, 0.1, 1e-4, 1e-5, 1e15, 1e16, 1e22, 5e-324, 1.7976931348623157e308])
    if k == 1:
        while True:
            x = struct.unpack("<d", struct.pack("<Q", r.getrandbits(64)))[0]
            if math.isfinite(x):
                return x
    if k == 2:
        return round(r.uniform(-1e6, 1e6), r.randrange(9))
    return r.random() * 10.0 ** r.randrange(-30, 30)


def rand_value(r, depth):
    k = r.randrange(9 if depth else 5)
    if k == 0:
        return "".join(rand_char(r) for _ in range(r.randrange(7)))
    if k == 1:
        return r.choice([0, -1, 7, 2**53, 2**63 - 1, -(2**63), 2**64, -(10**30), r.getrandbits(64) - 2**63])
    if k == 2:
        return rand_float(r)
    if k == 3:
        return r.random() < 0.5
    if k == 4:
        return None
    if k in (5, 6):
        return [rand_value(r, depth - 1) for _ in range(r.randrange(5))]
    return {r.choice(["a", "b", "é", ""]) if r.random() < 0.5 else
            "".join(rand_char(r) for _ in range(r.randrange(5))): rand_value(r, depth - 1)
            for _ in range(r.randrange(5))}


def check(text):
    """Whether ``exactjson check`` accepts the JSON Lines ``text``, and its message."""
    p = subprocess.run([str(EXE), "check"], input=text.encode(), capture_output=True)
    return p.returncode == 0, p.stderr.decode().strip()


def canon_lines(text):
    """``exactjson canon --lines`` of the JSON Lines ``text``: its exit code, output and message."""
    p = subprocess.run([str(EXE), "canon", "--lines"], input=text.encode(), capture_output=True)
    return p.returncode, p.stdout.decode(), p.stderr.decode().strip()


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


def same(a, b):
    """Equal as values, floats bit for bit and ints distinct from floats."""
    if type(a) is not type(b):
        return False
    if isinstance(a, float):
        return bits(a) == bits(b)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    return a == b


def read_typed(line):
    """json.loads, asserting integer tokens have no point and float tokens have one."""
    def as_int(token):
        assert not any(c in token for c in ".eE"), token
        return int(token)

    def as_float(token):
        assert "." in token, token
        return float(token)

    return json.loads(line, parse_int=as_int, parse_float=as_float)


def float_sweep(n, seed):
    r = random.Random(seed)
    xs = set()
    for e in range(-1074, 1024):
        x = math.ldexp(1.0, e)
        xs.update({x, math.nextafter(x, 0.0), math.nextafter(x, math.inf)})
    for k in range(-324, 309):
        x = float(f"1e{k}")
        xs.update({x, math.nextafter(x, 0.0), math.nextafter(x, math.inf)})
    for k in range(1, 20000):  # the smallest subnormals
        xs.add(k * 5e-324)
    xs.discard(math.inf)
    while len(xs) < n + 30000:
        x = struct.unpack("<d", struct.pack("<Q", r.getrandbits(64)))[0]
        if math.isfinite(x):
            xs.add(x)
    xs = sorted(xs) + [-x for x in sorted(xs)]
    lines = [dumps_float(x) for x in xs]
    ok, message = check("".join(line + "\n" for line in lines))
    if not ok:
        sys.exit(f"Lean rejects CPython's digits: {message}")
    for x, line in zip(xs, lines):
        if bits(float(line)) != bits(x):
            sys.exit(f"{line} does not read back as {x!r}")
    print(f"crosscheck: {len(xs)} floats: CPython's shortest digits are Lean's canonical text")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--count", type=int, default=5000)
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--floats", type=int, default=0)
    args = ap.parse_args()
    if args.floats:
        float_sweep(args.floats, args.seed)
        return
    r = random.Random(args.seed)
    values = [rand_value(r, 4) for _ in range(args.count)]
    lines = [dumps(v) for v in values]

    # 1. the Python writer writes what Lean writes
    ok, message = check("".join(line + "\n" for line in lines))
    if not ok:
        sys.exit(f"Lean rejects Python's canonical text: {message}")

    # 2. the lines read back as the same values, integer and float tokens apart
    for line, v in zip(lines, values):
        if not same(read_typed(line), v):
            sys.exit(f"{line} does not read back as its value")

    # 3. other spellings are rejected
    rejected = 0
    for v in values[:200]:
        other = json.dumps(v)  # spaces after , and :, ASCII escapes, keys unsorted
        if other != dumps(v):
            ok, _ = check(other + "\n")
            if ok:
                sys.exit(f"Lean accepts the non-canonical {other}")
            rejected += 1

    # 4. any JSON spelling of a value is read as it, and written canonically
    spellings = []
    for v in values:
        separators = r.choice([(",", ":"), (", ", ": "), (" , ", " : ")])
        spellings.append(json.dumps(v, separators=separators, ensure_ascii=r.random() < 0.5,
                                    sort_keys=r.random() < 0.5))
    code, out, message = canon_lines("".join(s + "\n" for s in spellings))
    if code != 0:
        sys.exit(f"Lean does not read Python's JSON: {message}")
    for spelling, line, got in zip(spellings, lines, out.split("\n")):
        if got != line:
            sys.exit(f"Lean reads {spelling} as {got}, not {line}")

    print(f"crosscheck: {len(values)} values agree byte for byte; {rejected} other spellings rejected; "
          f"{len(spellings)} JSON spellings canonicalized")


if __name__ == "__main__":
    main()
