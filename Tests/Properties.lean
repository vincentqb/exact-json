module

import TomlJson
meta import TomlJson

/-! Randomized checks of the format's laws, run when this module is built (`lake test`), with
fixed seeds so that a failure reproduces. For random values `v` (normal or not):

1. `Value.parse (render v) = v.normalize` and `render v.normalize = render v`;
2. `Value.parseCanonical (render v)` succeeds, and gives back the text;
3. any other spelling of `v.normalize` (whitespace, member order, escapes, number forms, `null`
   members) parses to `v.normalize`, and `parseCanonical` rejects it;
4. typed values: `decodeCanonical (encode a)` is `a`, and `decode` of any other spelling is too;
5. date-times print and parse back, Unix time converts both ways;
6. `Value.ofJson? v.toJson = v` (for values without `-0.0`).
-/

open TomlJson

/-! ## Randomness -/

/-- A splitmix64 generator. -/
structure Rng where
  /-- The state. -/
  state : UInt64

/-- The next word, and the next generator. -/
def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- Computations that draw random words. -/
abbrev Gen := StateM Rng

/-- A random word. -/
def word : Gen UInt64 := modifyGet Rng.next

/-- A random number below `n > 0`. -/
def below (n : Nat) : Gen Nat := return (← word).toNat % n

/-- A random item of a nonempty array. -/
def pick {α : Type} [Inhabited α] (xs : Array α) : Gen α := return xs[← below xs.size]!

/-- Run a generator from a seed. -/
def Gen.run' {α : Type} (g : Gen α) (seed : Nat) : α := (g.run ⟨seed.toUInt64⟩).1

/-! ## Values -/

/-- Characters that stress escaping. -/
def specialChars : Array Char :=
  #['"', '\\', '/', '\n', '\t', '\r', '\x08', '\x0c', '\x00', '\x1f', '\x7f', Char.ofNat 0x85,
    Char.ofNat 0x9f, Char.ofNat 0xa0, Char.ofNat 0x2028, Char.ofNat 0x2029, Char.ofNat 0xfeff,
    Char.ofNat 0xffff, Char.ofNat 0x10000, Char.ofNat 0x10ffff, 'é', '中', '😀']

/-- A random character. -/
def genChar : Gen Char := do
  match ← below 6 with
  | 0 => return Char.ofNat (0x20 + (← below 0x5f))
  | 1 => pick specialChars
  | 2 => return Char.ofNat (0xa0 + (← below (0xd800 - 0xa0)))
  | 3 => return Char.ofNat (0xe000 + (← below 0x2000))
  | 4 => return Char.ofNat (0x10000 + (← below 0x100000))
  | _ => return Char.ofNat (0x61 + (← below 26))

/-- A random string. -/
def genString : Gen String := do
  let n ← below 7
  let mut s := ""
  for _ in [0:n] do s := s.push (← genChar)
  return s

/-- Floats on boundaries. -/
def specialFloats : Array Float :=
  #[0.0, -0.0, 1.0, -1.0, 0.1, 0.5, 1e-4, 1e-5, 9.999999999999999e15, 1e16, 1e21, 1e22, 1e23,
    5e-324, 2.2250738585072014e-308, 2.225073858507201e-308, 1.7976931348623157e308,
    9007199254740992.0, 123456789.125, 0.30000000000000004]

/-- A random float, finite unless `nonFinite`. -/
def genFloat (nonFinite : Bool) : Gen Float := do
  match ← below 6 with
  | 0 => pick specialFloats
  | 1 => if nonFinite then pick #[0.0 / 0.0, 1.0 / 0.0, -1.0 / 0.0] else pick specialFloats
  | 2 => return Float.ofInt ((← below 2000001 : Nat) - 1000000) / Float.ofNat (10 ^ (← below 8))
  | 3 =>
    -- exponents near 1
    let w : UInt64 ← word
    let mask : UInt64 := 0x800FFFFFFFFFFFFF
    let e : UInt64 := (0x3C0 + (← below 0x80)).toUInt64 <<< 52
    return Float.ofBits ((w &&& mask) ||| e)
  | _ =>
    let bits ← word
    let x := Float.ofBits bits
    return if x.isNaN || x.isInf then 1.5 else x

/-- A random integer. -/
def genInt : Gen Int := do
  match ← below 4 with
  | 0 => return (← below 21 : Nat) - 10
  | 1 => pick #[0, -1, 2 ^ 53, 2 ^ 63 - 1, -(2 ^ 63), 2 ^ 64, -(10 ^ 30)]
  | 2 => return ((← word).toNat : Int) - 2 ^ 63
  | _ => return (← below 1000000 : Nat)

/-- A random value of nesting at most `depth`; with `normal := false` also NaNs, infinities and
tables with unsorted or repeated keys. -/
partial def genValue (depth : Nat) (normal : Bool) : Gen Value := do
  -- containers half the time while depth remains
  let choice ← below (if depth == 0 then 4 else 8)
  match choice with
  | 0 => return .string (← genString)
  | 1 => return .integer (← genInt)
  | 2 => return .float (← genFloat (!normal))
  | 3 => return .boolean ((← below 2) == 0)
  | 4 | 5 =>
    let n ← below 5
    let mut items := #[]
    for _ in [0:n] do items := items.push (← genValue (depth - 1) normal)
    return .array items
  | _ =>
    let n ← below 5
    let mut members := #[]
    for _ in [0:n] do
      -- short keys collide often, which exercises the last-wins rule
      let key ← if (← below 2) == 0 then pick #["a", "b", "A", "é", ""] else genString
      members := members.push (key, ← genValue (depth - 1) normal)
    let v := Value.table members
    return if normal then v.normalize else v

/-! ## Other spellings of a value -/

/-- Random JSON whitespace. -/
def genWs : Gen String := pick #["", "", "", " ", "\n", "\t", "\r\n", "  "]

/-- `n` as four hexadecimal digits, upper or lower case. -/
def hex4 (n : Nat) (upper : Bool) : String :=
  let d (k : Nat) : Char :=
    if k < 10 then Char.ofNat (48 + k) else Char.ofNat ((if upper then 55 else 87) + k)
  String.ofList [d (n / 4096 % 16), d (n / 256 % 16), d (n / 16 % 16), d (n % 16)]

/-- A random spelling of a string (escapes where JSON requires them, others at random). -/
def looseString (s : String) : Gen String := do
  let mut out := "\""
  for c in s.toList do
    let upper := (← below 2) == 0
    let u (n : Nat) := "\\u" ++ hex4 n upper
    if c.val < 0x20 || c == '"' || c == '\\' || (← below 4) == 0 then
      if c == '/' && (← below 2) == 0 then out := out ++ "\\/"
      else if c.val ≥ 0x10000 then
        let v := c.val.toNat - 0x10000
        out := out ++ u (0xD800 + v / 0x400) ++ u (0xDC00 + v % 0x400)
      else if (← below 2) == 0 then out := pushChar out c
      else out := out ++ u c.val.toNat
    else out := out.push c
  return out.push '"'

/-- A random spelling of a finite float: its shortest digits with the point anywhere, trailing
zeros, an exponent in any case and sign. -/
def looseFloat (x : Float) : Gen String := do
  let some d := FloatText.shortest x | return floatText x
  if (← below 4) == 0 then return floatText x
  let sign := if d.negative then "-" else ""
  let ds := (Nat.toDigits 10 d.digits) ++ List.replicate (← below 3) '0'
  let extra : Int := ds.length - (Nat.toDigits 10 d.digits).length
  -- value = ds × 10^(exponent - extra); write ds as `int.frac` with `k` fractional digits
  let k ← below (ds.length + 1)
  let intPart := ds.take (ds.length - k)
  let fracPart := ds.drop (ds.length - k)
  let e : Int := d.exponent - extra + k
  let intText := if intPart.isEmpty then "0" else String.ofList intPart
  -- a leading zero is allowed only as the whole integer part
  let intText := if intText.length > 1 && intText.startsWith "0" then "" else intText
  if intText.isEmpty then return floatText x
  let fracText := if fracPart.isEmpty then "" else "." ++ String.ofList fracPart
  let needExp := e != 0 || fracText.isEmpty
  let expText ←
    if needExp then do
      let mark ← pick #["e", "E"]
      let plus := if e ≥ 0 && (← below 2) == 0 then "+" else ""
      pure s!"{mark}{plus}{e}"
    else pure ""
  return sign ++ intText ++ fracText ++ expText

/-- Shuffle an array. -/
def shuffle {α : Type} [Inhabited α] (xs : Array α) : Gen (Array α) := do
  let mut xs := xs
  for i in [0:xs.size] do
    let j := i + (← below (xs.size - i))
    xs := xs.swapIfInBounds i j
  return xs

/-- A random spelling of a normal value. -/
partial def loose (v : Value) : Gen String := do
  let body ← match v with
    | .string s => looseString s
    | .integer n => do pure (if n == 0 && (← below 3) == 0 then "-0" else toString n)
    | .float x => looseFloat x
    | .boolean b => do pure (if b then "true" else "false")
    | .array items => do
      let mut out := "["
      for item in items, i in [0:items.size] do
        if i > 0 then out := out ++ (← genWs) ++ ","
        out := out ++ (← genWs) ++ (← loose item)
      pure (out ++ (← genWs) ++ "]")
    | .table members => do
      -- members in any order, perhaps with a `null` member (dropped when read)
      let mut members := (members.map fun (k, v) => (k, some v))
      if (← below 3) == 0 && (members.all (·.1 != "\x00null")) then
        members := members.push ("\x00null", none)
      let mut out := "{"
      for (k, v) in (← shuffle members), i in [0:members.size] do
        if i > 0 then out := out ++ (← genWs) ++ ","
        let text ← match v with
          | some v => loose v
          | none => pure "null"
        out := out ++ (← genWs) ++ (← looseString k) ++ (← genWs) ++ ":" ++ (← genWs) ++ text
      pure (out ++ (← genWs) ++ "}")
  return (← genWs) ++ body ++ (← genWs)

/-! ## Checks -/

/-- Fail with `msg` unless `ok`. -/
def check (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

/-- The value laws, for `count` random values from `seed`, nested at most `depth`. -/
def valueLaws (seed count depth : Nat) : IO Unit := do
  for i in [0:count] do
    let v := (genValue depth ((i % 3) != 0)).run' (seed + i)
    let text := v.render
    let n := v.normalize
    check (n.normalize == n && n.render == text) s!"normalize: {repr v}"
    match Value.parse text with
    | .ok w => check (w == n) s!"parse ∘ render ≠ normalize: {text}"
    | .error e => throw (IO.userError s!"parse failed on {text}: {e}")
    check (((Value.parseCanonical text).map Value.render).toOption == some text)
      s!"parseCanonical rejects {text}"
    -- other spellings of the same value
    for j in [0:3] do
      let other := (loose n).run' (seed * 7 + i * 3 + j)
      match Value.parse other with
      | .ok w => check (w == n) s!"{other} parses to {w.render}, not {text}"
      | .error e => throw (IO.userError s!"parse failed on {other}: {e}")
      check ((Value.parseCanonical other).isOk == (other == text)) s!"parseCanonical accepts {other}"

/-! ## Typed values -/

/-- A nested record. -/
structure Sample where
  /-- A label. -/
  label : String
  /-- A count. -/
  count : Nat
  /-- A measurement. -/
  value : Float
  /-- Optional. -/
  note? : Option String
  /-- Points. -/
  points : Array (Int × Float)
  /-- Children. -/
  children : List Sample
  /-- A day. -/
  day : LocalDate
  /-- A moment. -/
  stamp : OffsetDateTime
  deriving ToValue, FromValue, Inhabited

/-- A random valid date. -/
def genDate : Gen LocalDate := do
  let year ← below 10000
  let month := 1 + (← below 12)
  return { year, month, day := 1 + (← below (daysInMonth year month)) }

/-- A random valid time. -/
def genTime : Gen LocalTime := do
  let ns ← pick #[0, 0, 500000000, 1, 123456789, 999999999, 100]
  return { hour := ← below 24, minute := ← below 60, second := ← below 61, nanosecond := ns }

/-- A random valid offset date-time. -/
def genOffsetDateTime : Gen OffsetDateTime := do
  let offset ← pick #[0, 0, 60, -420, 330, 1439, -1439]
  return { date := ← genDate, time := ← genTime, offsetMinutes := offset }

/-- A random sample, nested at most `depth`. -/
partial def genSample (depth : Nat) : Gen Sample := do
  let k ← below 3
  let mut points := #[]
  for _ in [0:k] do points := points.push (← genInt, ← genFloat true)
  let mut children := []
  if depth > 0 then
    for _ in [0:(← below 3)] do children := (← genSample (depth - 1)) :: children
  let note ← genString
  let hasNote := (← below 2) == 0
  return { label := ← genString, count := ← below 1000, value := ← genFloat true,
           note? := if hasNote then some note else none,
           points, children, day := ← genDate, stamp := ← genOffsetDateTime }

/-- The typed laws, for `count` random samples. -/
def typedLaws (seed count : Nat) : IO Unit := do
  for i in [0:count] do
    let a := (genSample 2).run' (seed + i)
    let text := encode a
    match (decodeCanonical text : Except String Sample) with
    | .ok b => check (encode b == text) s!"decodeCanonical ∘ encode changes {text}"
    | .error e => throw (IO.userError s!"decodeCanonical rejects {text}: {e}")
    let other := (loose (toValue a)).run' (seed + 1000 + i)
    match (decode other : Except String Sample) with
    | .ok b => check (encode b == text) s!"decode {other} gives {encode b}"
    | .error e => throw (IO.userError s!"decode rejects {other}: {e}")

/-- Date-time laws. -/
def dateLaws (seed count : Nat) : IO Unit := do
  for i in [0:count] do
    let dt := genOffsetDateTime.run' (seed + i)
    for d in [DateTime.offsetDateTime dt, .localDateTime ⟨dt.date, dt.time⟩, .localDate dt.date,
        .localTime dt.time] do
      check (DateTime.parse? d.toString == some d) s!"date-time {d.toString}"
    -- Unix time both ways (UTC, no leap second)
    -- years about 70 to 9500
    let ns : Int := genInt.run' (seed + i) % 300000000000000000000 - 60000000000000000000
    match OffsetDateTime.ofUnixNanos? ns with
    | some utc => check (utc.toUnixNanos == ns && utc.isValid) s!"unix {ns} → {utc.toString}"
    | none => throw (IO.userError s!"unix {ns} is in range")

/-- `Lean.Json` both ways. -/
def leanJsonLaws (seed count : Nat) : IO Unit := do
  for i in [0:count] do
    let v := (genValue 4 true).run' (seed + i)
    -- a `JsonNumber` has no negative zero
    if (v.render.splitOn "-0.0").length > 1 then continue
    match Value.ofJson? v.toJson with
    | .ok w => check (w == v) s!"ofJson? ∘ toJson changes {v.render} into {w.render}"
    | .error e => throw (IO.userError s!"ofJson? fails on {v.render}: {e}")

#eval valueLaws 1 4000 4
#eval valueLaws 100000 300 7
#eval typedLaws 2 500
#eval dateLaws 3 2000
#eval leanJsonLaws 4 2000
