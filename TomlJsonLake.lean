module

public import TomlJson
public import Lake.Toml

/-! # Between `Value` and Lake's TOML

Lake reads TOML (`Lake.Toml.loadToml`) into `Lake.Toml.Value`, which has the same data model as
`Value` plus date-times. `Value.ofToml` writes each date-time as its canonical RFC 3339 string;
`Value.toToml` makes every string a TOML string (a `Value` cannot tell a date from a string, its
reader's type can).

Lake represents a TOML date-time as `Lake.Toml.DateTime`: an offset date-time (`Z` or a signed
`hh:mm` offset), a local date-time, a local date or a local time, the time as hour, minute,
second (60 allowed) and a decimal fraction of any length. `DateTime.ofLake` and `DateTime.toLake`
convert; a fraction beyond nanoseconds is truncated (as TOML says), and the three spellings of a
zero offset (`Z`, `+00:00`, `-00:00`) all become `Z`.

Note: Lake's own TOML printer (`Lake.Toml.ppTable`) writes floats with `Float.toString`, six fixed
decimals (`1e-7` is written `0.000000`), and writes a fraction of a second with a leading zero
wrong (`00:00:00.05` as `00:00:00.500`); reading is right, and so is this module's JSON.
-/

public section

namespace TomlJson

/-- A Lake time, to the nanosecond (a longer fraction is truncated).

Lake's parser (v4.36) stores a fraction of `n` digits as `fracMantissa` with
`fracExponent = n - 1`: `.05` is mantissa 5, exponent 1. (Its printer pads the mantissa to
`fracExponent` digits, so it writes `.05` back as `.500`.) -/
def LocalTime.ofLake (t : Lake.Toml.Time) : LocalTime :=
  let digits := t.fracExponent + 1
  let ns :=
    if t.fracMantissa == 0 then 0
    else if digits ≤ 9 then t.fracMantissa * 10 ^ (9 - digits)
    else t.fracMantissa / 10 ^ (digits - 9)
  { hour := t.hour, minute := t.minute, second := t.second, nanosecond := ns }

/-- A time as Lake's parser would read its canonical text (see `LocalTime.ofLake`). -/
def LocalTime.toLake (t : LocalTime) : Lake.Toml.Time :=
  let base : Lake.Toml.Time := { hour := t.hour, minute := t.minute, second := t.second }
  if t.nanosecond == 0 then base
  else
    let digits := (Nat.toDigits 10 (t.nanosecond + 1000000000)).drop 1
    let digits := (digits.reverse.dropWhile (· == '0')).reverse
    { base with fracExponent := digits.length - 1,
                fracMantissa := digits.foldl (fun n c => n * 10 + (c.toNat - 48)) 0 }

/-- A Lake date. -/
def LocalDate.ofLake (d : Lake.Date) : LocalDate := { year := d.year, month := d.month, day := d.day }

/-- A date as Lake's. -/
def LocalDate.toLake (d : LocalDate) : Lake.Date := { year := d.year, month := d.month, day := d.day }

/-- A Lake date-time. -/
def DateTime.ofLake : Lake.Toml.DateTime → DateTime
  | .offsetDateTime d t offset? =>
    let minutes : Int := match offset? with
      | none => 0
      | some (negative, o) =>
        let m : Int := o.hour * 60 + o.minute
        if negative then -m else m
    .offsetDateTime { date := .ofLake d, time := .ofLake t, offsetMinutes := minutes }
  | .localDateTime d t => .localDateTime { date := .ofLake d, time := .ofLake t }
  | .localDate d => .localDate (.ofLake d)
  | .localTime t => .localTime (.ofLake t)

/-- A date-time as Lake's (a zero offset as `Z`). -/
def DateTime.toLake : DateTime → Lake.Toml.DateTime
  | .offsetDateTime dt =>
    let offset? : Option (Bool × Lake.Toml.Time) :=
      if dt.offsetMinutes == 0 then none
      else
        let m := dt.offsetMinutes.natAbs
        some (dt.offsetMinutes < 0, { hour := m / 60, minute := m % 60, second := 0 })
    .offsetDateTime dt.date.toLake dt.time.toLake offset?
  | .localDateTime dt => .localDateTime dt.date.toLake dt.time.toLake
  | .localDate d => .localDate d.toLake
  | .localTime t => .localTime t.toLake

/-- A table key from Lake's: a one-part name is its string. -/
private def keyOfName : Lean.Name → String
  | .str .anonymous s => s
  | n => n.toString (escape := false)

namespace Value

/-- The value of a Lake TOML value: date-times as their canonical strings, non-finite floats as
their names. -/
partial def ofToml : Lake.Toml.Value → Value
  | .string _ s => .string s
  | .integer _ n => .integer n
  | .float _ x => (Value.float x).normalize
  | .boolean _ b => .boolean b
  | .dateTime _ dt => .string (DateTime.ofLake dt).toString
  | .array _ items => .array (items.map ofToml)
  | .table _ t => .table (sortMembers (t.items.map fun (k, v) => (keyOfName k, ofToml v)))

/-- A value as a Lake TOML value (every string a string). -/
partial def toToml : Value → Lake.Toml.Value
  | .string s => .string .missing s
  | .integer n => .integer .missing n
  | .float x => .float .missing x
  | .boolean b => .boolean .missing b
  | .array items => .array .missing (items.map toToml)
  | .table members =>
    .table .missing ((sortMembers members).foldl (init := {}) fun t (k, v) =>
      t.insert (Lean.Name.mkSimple k) (toToml v))

end Value

/-- The value of a TOML document (a table), or Lake's error messages. -/
def ofTomlText (text : String) (fileName := "<toml>") : IO (Except String Value) := do
  let ictx := Lean.Parser.mkInputContext text fileName
  match ← (Lake.Toml.loadToml ictx).toBaseIO with
  | .ok table => return .ok (Value.ofToml (.table .missing table))
  | .error log =>
    let msgs ← log.toList.mapM fun m => m.toString
    return .error (String.intercalate "\n" msgs)

end TomlJson
