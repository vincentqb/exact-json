"""Cross-check the Lean implementation against Python's json module and the reference encoder.

    lake build tomljson && python3 python/crosscheck.py [--count N] [--seed S]

1. Random Python values, written by the reference ``dumps``, are canonical to ``tomljson check``.
2. The same values written by plain ``json.dumps`` (spaces, ASCII escapes, unsorted keys, Python's
   float repr), through ``tomljson canon``, come out exactly as ``dumps`` writes them.
3. Every canonical line reads back with ``json.loads`` as the same value: integers as ``int``
   from tokens without a point, floats as ``float`` from tokens with one, bit for bit.
4. ``str.splitlines`` on canonical JSON Lines finds exactly one line per value.

With ``--floats N``, instead: every power of two and of ten and their neighbours, the subnormal
boundaries and N random bit patterns, through ``tomljson canon``, are written as ``dumps_float``
writes them (CPython's ``repr`` digits) and read back bit for bit.
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
from tomljson import dumps, dumps_float, loads  # noqa: E402

EXE = Path(__file__).resolve().parent.parent / ".lake" / "build" / "bin" / "tomljson"

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
    k = r.randrange(8 if depth else 4)
    if k == 0:
        return "".join(rand_char(r) for _ in range(r.randrange(7)))
    if k == 1:
        return r.choice([0, -1, 7, 2**53, 2**63 - 1, -(2**63), 2**64, -(10**30), r.getrandbits(64) - 2**63])
    if k == 2:
        return rand_float(r)
    if k == 3:
        return r.random() < 0.5
    if k in (4, 5):
        return [rand_value(r, depth - 1) for _ in range(r.randrange(5))]
    return {r.choice(["a", "b", "é", ""]) if r.random() < 0.5 else
            "".join(rand_char(r) for _ in range(r.randrange(5))): rand_value(r, depth - 1)
            for _ in range(r.randrange(5))}


def run(command, text):
    p = subprocess.run([str(EXE), command], input=text.encode(), capture_output=True)
    if p.returncode != 0:
        sys.exit(f"tomljson {command} failed: {p.stderr.decode()}")
    return p.stdout.decode()


def same(a, b):
    """Equal as values, floats bit for bit and ints distinct from floats."""
    if type(a) is not type(b):
        return False
    if isinstance(a, float):
        return struct.pack("<d", a) == struct.pack("<d", b)
    if isinstance(a, list):
        return len(a) == len(b) and all(same(x, y) for x, y in zip(a, b))
    if isinstance(a, dict):
        return a.keys() == b.keys() and all(same(a[k], b[k]) for k in a)
    return a == b


def check_tokens(line):
    """json.loads, asserting integer tokens have no point and float tokens have one."""
    def as_int(token):
        assert not any(c in token for c in ".eE"), token
        return int(token)

    def as_float(token):
        assert "." in token, token
        return float(token)

    return json.loads(line, parse_int=as_int, parse_float=as_float)


def bits(x):
    return struct.unpack("<Q", struct.pack("<d", x))[0]


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
    lean = run("canon", "".join(json.dumps(x) + "\n" for x in xs)).split("\n")[:-1]
    for x, text in zip(xs, lean):
        if text != dumps_float(x) or bits(float(text)) != bits(x):
            sys.exit(f"float {x!r} ({bits(x):#x}): Lean writes {text}, expected {dumps_float(x)}")
    print(f"crosscheck: {len(xs)} floats: Lean writes CPython's shortest digits, read back exactly")


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
    canonical = "".join(dumps(v) + "\n" for v in values)

    # 1. the reference encoder writes canonical text
    run("check", canonical)

    # 2. plain json.dumps text, canonicalized by Lean, is the reference encoder's text
    plain = "".join(json.dumps(v) + "\n" for v in values)
    lean = run("canon", plain)
    if lean != canonical:
        for i, (a, b) in enumerate(zip(lean.split("\n"), canonical.split("\n"))):
            if a != b:
                sys.exit(f"line {i + 1} differs:\n lean:   {a}\n python: {b}")
        sys.exit("outputs differ in length")

    # 3. canonical lines read back as the same values, with int and float tokens apart
    lines = lean.split("\n")[:-1]
    for line, v in zip(lines, values):
        if not same(check_tokens(line), json.loads(dumps(v))):
            sys.exit(f"{line} does not read back as its value")

    # 4. no line breaks inside a line, for any line splitter
    if len(lean.splitlines()) != len(values):
        sys.exit("str.splitlines splits a canonical line")

    # 5. the Python reader agrees: what Lean wrote reads back and writes again to the same line
    for line in lines:
        if dumps(loads(line)) != line:
            sys.exit(f"python round trip changes {line}")

    print(f"crosscheck: {len(values)} values, {len(lean)} characters: Lean and Python agree")


if __name__ == "__main__":
    main()
