module

import ExactJSON
meta import ExactJSON

open ExactJSON

def parseText (s : String) : Except String Value := Value.read .canonical 10000 s.toUTF8

def readText (s : String) : Except String Value := Value.read .any 10000 s.toUTF8

def decodeText {α : Type} [ToValue α] [FromValue α] (s : String) : Except String α := decode 10000 s.toUTF8

def linesText (s : String) : Except String (Array Value) := Value.readLines .canonical 10000 s.toUTF8

structure Rng where
  state : UInt64

def Rng.next (r : Rng) : UInt64 × Rng :=
  let s := r.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

abbrev Gen := StateM Rng

def word : Gen UInt64 := modifyGet Rng.next

def below (n : Nat) : Gen Nat := return (← word).toNat % n

def pick {α : Type} [Inhabited α] (xs : Array α) : Gen α := return xs[← below xs.size]!

def Gen.run' {α : Type} (g : Gen α) (seed : Nat) : α := (g.run ⟨seed.toUInt64⟩).1

def specialChars : Array Char :=
  #['"', '\\', '/', '\n', '\t', '\r', '\x08', '\x0c', '\x00', '\x1f', '\x7f', Char.ofNat 0x85,
    Char.ofNat 0x9f, Char.ofNat 0xa0, Char.ofNat 0x2028, Char.ofNat 0x2029, Char.ofNat 0xfeff,
    Char.ofNat 0xffff, Char.ofNat 0x10000, Char.ofNat 0x10ffff, 'é', '中', '😀']

def genChar : Gen Char := do
  match ← below 6 with
  | 0 => return Char.ofNat (0x20 + (← below 0x5f))
  | 1 => pick specialChars
  | 2 => return Char.ofNat (0xa0 + (← below (0xd800 - 0xa0)))
  | 3 => return Char.ofNat (0xe000 + (← below 0x2000))
  | 4 => return Char.ofNat (0x10000 + (← below 0x100000))
  | _ => return Char.ofNat (0x61 + (← below 26))

def genString : Gen String := do
  let n ← below 7
  let mut s := ""
  for _ in [0:n] do s := s.push (← genChar)
  return s

def specialFloats : Array Float :=
  #[0.0, -0.0, 1.0, -1.0, 0.1, 0.5, 1e-4, 1e-5, 9.999999999999999e15, 1e16, 1e21, 1e22, 1e23,
    5e-324, 2.2250738585072014e-308, 2.225073858507201e-308, 1.7976931348623157e308,
    9007199254740992.0, 123456789.125, 0.30000000000000004]

def genFloat (nonFinite : Bool) : Gen Float := do
  match ← below 6 with
  | 0 => pick specialFloats
  | 1 => if nonFinite then pick #[0.0 / 0.0, 1.0 / 0.0, -1.0 / 0.0] else pick specialFloats
  | 2 => return Float.ofInt ((← below 2000001 : Nat) - 1000000) / Float.ofNat (10 ^ (← below 8))
  | 3 =>
    let w : UInt64 ← word
    let mask : UInt64 := 0x800FFFFFFFFFFFFF
    let e : UInt64 := (0x3C0 + (← below 0x80)).toUInt64 <<< 52
    return Float.ofBits ((w &&& mask) ||| e)
  | _ =>
    let bits ← word
    let x := Float.ofBits bits
    return if x.isNaN || x.isInf then 1.5 else x

def genInt : Gen Int := do
  match ← below 4 with
  | 0 => return (← below 21 : Nat) - 10
  | 1 => pick #[0, -1, 2 ^ 53, 2 ^ 63 - 1, -(2 ^ 63), 2 ^ 64, -(10 ^ 30)]
  | 2 => return ((← word).toNat : Int) - 2 ^ 63
  | _ => return (← below 1000000 : Nat)

def genDecimal : Gen Decimal := do
  match ← below 3 with
  | 0 => return (FloatText.shortest (← genFloat false)).getD ⟨false, 15, -1⟩
  | 1 =>
    let m ← below 100000
    let zeros ← below 4
    return Decimal.normalize ((← below 2) == 0) (m * 10 ^ zeros) (((← below 801 : Nat) : Int) - 400)
  | _ =>
    let m := (← word).toNat * 2 ^ 64 + (← word).toNat
    return Decimal.normalize ((← below 2) == 0) m (((← below 4001 : Nat) : Int) - 2000)

partial def genValue (depth : Nat) : Gen Value := do
  let choice ← below (if depth == 0 then 5 else 9)
  match choice with
  | 0 => return .string (← genString)
  | 1 => return .integer (← genInt)
  | 2 => return .decimal (← genDecimal)
  | 3 => return .boolean ((← below 2) == 0)
  | 4 => return .null
  | 5 | 6 =>
    let n ← below 5
    let mut items := #[]
    for _ in [0:n] do items := items.push (← genValue (depth - 1))
    return .array items
  | _ =>
    let n ← below 5
    let mut members : Array (String × Value) := #[]
    for _ in [0:n] do
      let key ← if (← below 2) == 0 then pick #["a", "b", "A", "é", ""] else genString
      if members.all (·.1 != key) then members := members.push (key, ← genValue (depth - 1))
    return .table (members.qsort (·.1 < ·.1))

def genInvalid (depth : Nat) : Gen Value := do
  let v ← genValue depth
  match ← below 3 with
  | 0 => return .array #[v, .decimal (← pick #[⟨false, 150, -2⟩, ⟨false, 10, 0⟩, ⟨true, 0, 3⟩, ⟨false, 0, -1⟩])]
  | 1 => return .table #[("b", v), ("a", v)]
  | _ => return .table #[("a", v), ("a", v)]

def genWs : Gen String := pick #["", "", "", " ", "\n", "\t", "\r\n", "  "]

def hex4 (n : Nat) (upper : Bool) : String :=
  let d (k : Nat) : Char :=
    if k < 10 then Char.ofNat (48 + k) else Char.ofNat ((if upper then 55 else 87) + k)
  String.ofList [d (n / 4096 % 16), d (n / 256 % 16), d (n / 16 % 16), d (n % 16)]

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

def looseDecimal (d : Decimal) : Gen String := do
  if (← below 4) == 0 then return d.text
  let sign := if d.negative then "-" else ""
  let ds := (Nat.toDigits 10 d.digits) ++ List.replicate (← below 3) '0'
  let extra : Int := ds.length - (Nat.toDigits 10 d.digits).length
  let k ← below (ds.length + 1)
  let intPart := ds.take (ds.length - k)
  let fracPart := ds.drop (ds.length - k)
  let e : Int := d.exponent - extra + k
  let intText := if intPart.isEmpty then "0" else String.ofList intPart
  let intText := if intText.length > 1 && intText.startsWith "0" then "" else intText
  if intText.isEmpty then return d.text
  let fracText := if fracPart.isEmpty then "" else "." ++ String.ofList fracPart
  let needExp := e != 0 || fracText.isEmpty
  let expText ←
    if needExp then do
      let mark ← pick #["e", "E"]
      let plus := if e ≥ 0 && (← below 2) == 0 then "+" else ""
      pure s!"{mark}{plus}{e}"
    else pure ""
  return sign ++ intText ++ fracText ++ expText

def shuffle {α : Type} [Inhabited α] (xs : Array α) : Gen (Array α) := do
  let mut xs := xs
  for i in [0:xs.size] do
    let j := i + (← below (xs.size - i))
    xs := xs.swapIfInBounds i j
  return xs

partial def loose (v : Value) : Gen String := do
  let body ← match v with
    | .string s => looseString s
    | .integer n => do pure (if n == 0 && (← below 3) == 0 then "-0" else toString n)
    | .decimal d => looseDecimal d
    | .boolean b => do pure (if b then "true" else "false")
    | .null => do pure "null"
    | .array items => do
      let mut out := "["
      for item in items, i in [0:items.size] do
        if i > 0 then out := out ++ (← genWs) ++ ","
        out := out ++ (← genWs) ++ (← loose item)
      pure (out ++ (← genWs) ++ "]")
    | .table members => do
      let mut out := "{"
      for (k, v) in (← shuffle members), i in [0:members.size] do
        if i > 0 then out := out ++ (← genWs) ++ ","
        out := out ++ (← genWs) ++ (← looseString k) ++ (← genWs) ++ ":" ++ (← genWs) ++ (← loose v)
      pure (out ++ (← genWs) ++ "}")
  return (← genWs) ++ body ++ (← genWs)

def check (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw (IO.userError msg)

def valueLaws (seed count depth : Nat) : IO Unit := do
  for i in [0:count] do
    let v := (genValue depth).run' (seed + i)
    let text := v.render
    check v.isValid s!"generated an invalid value: {text}"
    match parseText text with
    | .ok w => check (w == v) s!"parse ∘ render changes {text} into {w.render}"
    | .error e => throw (IO.userError s!"parse rejects the canonical {text}: {e}")
    match readText text with
    | .ok w => check (w == v) s!"readJson changes {text} into {w.render}"
    | .error e => throw (IO.userError s!"readJson rejects the canonical {text}: {e}")
    for j in [0:3] do
      let other := (loose v).run' (seed * 7 + i * 3 + j)
      match parseText other with
      | .ok w => check (other == text && w == v) s!"parse accepts the non-canonical {other}"
      | .error _ => check (other != text) s!"parse rejects the canonical {text}"
      match readText other with
      | .ok w => check (w == v) s!"readJson reads {other} as {w.render}, not {text}"
      | .error e => throw (IO.userError s!"readJson rejects the JSON {other}: {e}")
    let bad := (genInvalid (depth - 1)).run' (seed + 5 * i)
    check (!bad.isValid && (parseText bad.render).toOption != some bad) s!"an invalid value is read: {bad.render}"

structure Sample where
  label : String
  count : Nat
  value : Float
  note? : Option String
  points : Array (Int × Float)
  readings : Array (Option Float)
  day : LocalDate
  stamp : OffsetDateTime
  deriving ToValue, FromValue, LawfulValue, Inhabited

def genDate : Gen LocalDate := do
  let year ← below 10000
  let month := 1 + (← below 12)
  let day := 1 + (← below (daysInMonth year month))
  return if h : LocalDate.Valid year month day then ⟨year, month, day, h⟩ else default

def genTime : Gen LocalTime := do
  let ns ← pick #[0, 0, 500000000, 1, 123456789, 999999999, 100]
  let hour ← below 24
  let minute ← below 60
  let second ← below 61
  return if h : LocalTime.Valid hour minute second ns then ⟨hour, minute, second, ns, h⟩ else default

def genOffsetDateTime : Gen OffsetDateTime := do
  let offset ← pick #[0, 0, 60, -420, 330, 1439, -1439]
  let date ← genDate
  let time ← genTime
  return if h : offset.natAbs < 24 * 60 then ⟨date, time, offset, h⟩ else { date, time }

def genSample : Gen Sample := do
  let k ← below 3
  let mut points := #[]
  for _ in [0:k] do points := points.push (← genInt, ← genFloat true)
  let mut readings := #[]
  for _ in [0:(← below 4)] do
    let x ← genFloat true
    readings := readings.push (if (← below 3) == 0 then none else some x)
  let note ← genString
  let hasNote := (← below 2) == 0
  return { label := ← genString, count := ← below 1000, value := ← genFloat true,
           note? := if hasNote then some note else none,
           points, readings, day := ← genDate, stamp := ← genOffsetDateTime }

structure SampleV2 extends Sample where
  added? : Option String
  deriving ToValue, FromValue

def setKey (v : Value) (key : String) (x : Value) : Value :=
  match v with
  | .table members =>
    .table ((members.filter (·.1 != key)).push (key, x) |>.qsort (·.1 < ·.1))
  | v => v

def instanceLaws (seed count : Nat) : IO Unit := do
  for i in [0:count] do
    let a := genSample.run' (seed + i)
    let v := toValue a
    match (fromValue? v : Except String Sample) with
    | .ok b => check (toValue b == v) s!"fromValue? ∘ toValue changes {v.render}"
    | .error e => throw (IO.userError s!"fromValue? rejects {v.render}: {e}")
    let bad := [setKey v "zz" .null, setKey v "count" (.decimal ⟨false, 1, 0⟩), setKey v "label" (.integer 1)] ++
      (if a.note?.isNone then [setKey v "note" .null] else [])
    for w in bad do
      check (!(fromValue? w : Except String Sample).isOk) s!"fromValue? accepts {w.render}"

def typedLaws (seed count : Nat) : IO Unit := do
  for i in [0:count] do
    let a := genSample.run' (seed + i)
    let text := encode a
    match (decodeText text : Except String Sample) with
    | .ok b => check (encode b == text) s!"decode ∘ encode changes {text}"
    | .error e => throw (IO.userError s!"decode rejects {text}: {e}")
    let other := (loose (toValue a)).run' (seed + 1000 + i)
    check ((decodeText other : Except String Sample).isOk == (other == text)) s!"decode accepts {other}"
    let a2 : SampleV2 := { toSample := a, added? := none }
    check (encode a2 == text) s!"adding an Option field changed {text}"
    match (decodeText text : Except String SampleV2) with
    | .ok b => check (b.added?.isNone && encode b.toSample == text) s!"the new type reads {text} wrongly"
    | .error e => throw (IO.userError s!"the new type rejects the old text {text}: {e}")

def dateLaws (seed count : Nat) : IO Unit := do
  for i in [0:count] do
    let dt := genOffsetDateTime.run' (seed + i)
    for d in [DateTime.offsetDateTime dt, .localDateTime ⟨dt.date, dt.time⟩, .localDate dt.date,
        .localTime dt.time] do
      check (DateTime.parse? d.toString == some d) s!"date-time {d.toString}"

#eval valueLaws 1 4000 4
#eval valueLaws 100000 300 7
#eval typedLaws 2 500
#eval instanceLaws 7 500
#eval dateLaws 3 2000
