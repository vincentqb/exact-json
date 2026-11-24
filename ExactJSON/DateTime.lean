module

public import ExactJSON.Codec
public import Std.Time.DateTime.Timestamp
import Std.Time.Zoned

/-! # Date-times as strings

JSON has no date-time type, so a date-time is a string in one canonical RFC 3339 form, and its
Lean type says how to read it back. The four kinds (RFC 3339's date-time and its parts):

| kind             | Lean type         | canonical text                     |
|------------------|-------------------|------------------------------------|
| offset date-time | `OffsetDateTime`  | `1979-05-27T07:32:00Z`, `1979-05-27T00:32:00.999999-07:00` |
| local date-time  | `LocalDateTime`   | `1979-05-27T07:32:00`              |
| date             | `LocalDate`       | `1979-05-27`                       |
| time of day      | `LocalTime`       | `07:32:00`, `00:32:00.5`           |

An upper-case `T`; seconds always written; a fraction only when nonzero, with no trailing zero
(to the nanosecond); a zero offset as `Z`, any other as `±HH:MM`. Reading takes this form and no
other.

The structures do not enforce their ranges; `isValid` says whether a value is a real date-time.
Valid values read back as themselves; an invalid one is written as text the reader rejects, never
as some other date-time.
-/

public section

namespace ExactJSON

/-- A calendar date, proleptic Gregorian, years 0 to 9999. -/
structure LocalDate where
  /-- The year, 0 to 9999. -/
  year : Nat
  /-- The month, 1 to 12. -/
  month : Nat
  /-- The day of the month, from 1. -/
  day : Nat
  deriving DecidableEq, Ord, Repr, Inhabited

/-- A time of day, to the nanosecond. Second 60 is a leap second, as RFC 3339
allows. -/
structure LocalTime where
  /-- The hour, 0 to 23. -/
  hour : Nat
  /-- The minute, 0 to 59. -/
  minute : Nat
  /-- The second, 0 to 60. -/
  second : Nat
  /-- The nanoseconds past the second, below 10⁹. -/
  nanosecond : Nat := 0
  deriving DecidableEq, Ord, Repr, Inhabited

/-- A date and a time of day, with no offset. -/
structure LocalDateTime where
  /-- The date. -/
  date : LocalDate
  /-- The time of day. -/
  time : LocalTime
  deriving DecidableEq, Ord, Repr, Inhabited

/-- A date and time of day at an offset from UTC (an RFC 3339 date-time). -/
structure OffsetDateTime where
  /-- The local date. -/
  date : LocalDate
  /-- The local time of day. -/
  time : LocalTime
  /-- The local time's offset from UTC, in minutes, below 24 hours either way; 0 is `Z`. -/
  offsetMinutes : Int := 0
  deriving DecidableEq, Repr, Inhabited

/-- Any of the four kinds of date-time. -/
inductive DateTime where
  /-- An offset date-time. -/
  | offsetDateTime (dt : OffsetDateTime)
  /-- A local date-time. -/
  | localDateTime (dt : LocalDateTime)
  /-- A local date. -/
  | localDate (d : LocalDate)
  /-- A local time. -/
  | localTime (t : LocalTime)
  deriving DecidableEq, Repr, Inhabited

/-! ## Validity -/

/-- Whether `y` is a Gregorian leap year. -/
def isLeapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

/-- The number of days in month `m` of year `y`. -/
def daysInMonth (y m : Nat) : Nat :=
  if m == 2 then (if isLeapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

/-- Whether the date exists and has a four-digit year. -/
def LocalDate.isValid (d : LocalDate) : Bool :=
  d.year ≤ 9999 && 1 ≤ d.month && d.month ≤ 12 && 1 ≤ d.day && d.day ≤ daysInMonth d.year d.month

/-- Whether the fields are in range. -/
def LocalTime.isValid (t : LocalTime) : Bool :=
  t.hour ≤ 23 && t.minute ≤ 59 && t.second ≤ 60 && t.nanosecond < 1000000000

/-- Whether the date and the time are valid. -/
def LocalDateTime.isValid (dt : LocalDateTime) : Bool := dt.date.isValid && dt.time.isValid

/-- Whether the date and time are valid and the offset below 24 hours. -/
def OffsetDateTime.isValid (dt : OffsetDateTime) : Bool :=
  dt.date.isValid && dt.time.isValid && dt.offsetMinutes.natAbs < 24 * 60

/-! ## Writing -/

/-- `n` in decimal, padded with zeros to `width` digits. -/
private def pad (width n : Nat) : String :=
  let ds := Nat.toDigits 10 n
  String.ofList (List.replicate (width - ds.length) '0' ++ ds)

/-- `YYYY-MM-DD`. -/
protected def LocalDate.toString (d : LocalDate) : String :=
  s!"{pad 4 d.year}-{pad 2 d.month}-{pad 2 d.day}"

/-- `HH:MM:SS`, then `.` and the fraction's digits without trailing zeros if it is nonzero. A
nanosecond field of 10⁹ or more has no fraction to write; it is written so that no reader takes
it (as every other invalid field is), not as some other time. -/
protected def LocalTime.toString (t : LocalTime) : String :=
  let base := s!"{pad 2 t.hour}:{pad 2 t.minute}:{pad 2 t.second}"
  if t.nanosecond == 0 then base
  else if t.nanosecond ≥ 1000000000 then s!"{base} (nanosecond {t.nanosecond} out of range)"
  else
    let digits := (pad 9 t.nanosecond).toList.reverse.dropWhile (· == '0') |>.reverse
    base ++ "." ++ String.ofList digits

/-- The date, `T`, the time. -/
protected def LocalDateTime.toString (dt : LocalDateTime) : String :=
  s!"{dt.date.toString}T{dt.time.toString}"

/-- `Z` for a zero offset, `±HH:MM` for any other. -/
def offsetText (minutes : Int) : String :=
  if minutes == 0 then "Z"
  else
    let sign := if minutes < 0 then "-" else "+"
    let m := minutes.natAbs
    s!"{sign}{pad 2 (m / 60)}:{pad 2 (m % 60)}"

/-- The date, `T`, the time, the offset. -/
protected def OffsetDateTime.toString (dt : OffsetDateTime) : String :=
  s!"{dt.date.toString}T{dt.time.toString}{offsetText dt.offsetMinutes}"

/-- The canonical text of any date-time. -/
protected def DateTime.toString : DateTime → String
  | .offsetDateTime dt => dt.toString
  | .localDateTime dt => dt.toString
  | .localDate d => d.toString
  | .localTime t => t.toString

instance : ToString LocalDate := ⟨LocalDate.toString⟩
instance : ToString LocalTime := ⟨LocalTime.toString⟩
instance : ToString LocalDateTime := ⟨LocalDateTime.toString⟩
instance : ToString OffsetDateTime := ⟨OffsetDateTime.toString⟩
instance : ToString DateTime := ⟨DateTime.toString⟩

/-! ## Reading -/

namespace DateText

/-- `n` decimal digits at the front of `cs`, their value and the rest. -/
private def fixed (n : Nat) (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.take n
  if ds.length == n && ds.all Char.isDigit then
    some (ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0, cs.drop n)
  else none

/-- `c` at the front of `cs`, and the rest. -/
private def lit (c : Char) : List Char → Option (List Char)
  | d :: rest => if c == d then some rest else none
  | [] => none

/-- A date `YYYY-MM-DD` at the front, and the rest. -/
private def date (cs : List Char) : Option (LocalDate × List Char) := do
  let (year, cs) ← fixed 4 cs
  let cs ← lit '-' cs
  let (month, cs) ← fixed 2 cs
  let cs ← lit '-' cs
  let (day, cs) ← fixed 2 cs
  let d : LocalDate := { year, month, day }
  if d.isValid then some (d, cs) else none

/-- A time `HH:MM:SS[.F…]` at the front (at most nine fractional digits), and the rest. -/
private def time (cs : List Char) : Option (LocalTime × List Char) := do
  let (hour, cs) ← fixed 2 cs
  let cs ← lit ':' cs
  let (minute, cs) ← fixed 2 cs
  let cs ← lit ':' cs
  let (second, cs) ← fixed 2 cs
  let (nanosecond, cs) ←
    match lit '.' cs with
    | none => some (0, cs)
    | some cs =>
      let ds := cs.takeWhile Char.isDigit
      if ds.isEmpty || ds.length > 9 then none
      some ((ds ++ List.replicate (9 - ds.length) '0').foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0,
        cs.drop ds.length)
  let t : LocalTime := { hour, minute, second, nanosecond }
  if t.isValid then some (t, cs) else none

/-- An offset `Z` or `±HH:MM` at the front, in minutes, and the rest. -/
private def offset (cs : List Char) : Option (Int × List Char) :=
  match cs with
  | 'Z' :: rest => some (0, rest)
  | s :: rest =>
    if s == '+' || s == '-' then do
      let (h, rest) ← fixed 2 rest
      let rest ← lit ':' rest
      let (m, rest) ← fixed 2 rest
      if h ≤ 23 && m ≤ 59 then
        some ((if s == '-' then -1 else 1) * ((h * 60 + m : Nat) : Int), rest)
      else none
    else none
  | [] => none

/-- A date-time of any kind, the whole text, by shape. -/
private def shape (s : String) : Option DateTime :=
  let cs := s.toList
  match date cs with
  | some (d, []) => some (.localDate d)
  | some (d, 'T' :: rest) =>
    match time rest with
    | some (t, []) => some (.localDateTime { date := d, time := t })
    | some (t, rest) =>
      match offset rest with
      | some (o, []) => some (.offsetDateTime { date := d, time := t, offsetMinutes := o })
      | _ => none
    | none => none
  | some _ => none
  | none =>
    match time cs with
    | some (t, []) => some (.localTime t)
    | _ => none

end DateText

/-- The date-time whose canonical text is `s`, if it is one: `parse? s = some dt` exactly when
`dt` is valid and `dt.toString = s`. -/
def DateTime.parse? (s : String) : Option DateTime :=
  -- The shape takes trailing zeros and `+00:00`; the canonical text does not.
  (DateText.shape s).filter (·.toString == s)

/-! ## As values -/

instance : ToValue DateTime := ⟨fun dt => .string dt.toString⟩
instance : FromValue DateTime where
  fromValue?
    | .string s => match DateTime.parse? s with
      | some dt => pure dt
      | none => typeMismatch "a date-time, date or time in canonical RFC 3339 form" (.string s)
    | v => typeMismatch "a date-time string" v

instance : ToValue OffsetDateTime := ⟨fun dt => .string dt.toString⟩
instance : FromValue OffsetDateTime where
  fromValue? v := do
    match ← (fromValue? v : Except String DateTime) with
    | .offsetDateTime dt => pure dt
    | _ => typeMismatch "an offset date-time (with Z or ±HH:MM)" v

instance : ToValue LocalDateTime := ⟨fun dt => .string dt.toString⟩
instance : FromValue LocalDateTime where
  fromValue? v := do
    match ← (fromValue? v : Except String DateTime) with
    | .localDateTime dt => pure dt
    | _ => typeMismatch "a local date-time (no offset)" v

instance : ToValue LocalDate := ⟨fun d => .string d.toString⟩
instance : FromValue LocalDate where
  fromValue? v := do
    match ← (fromValue? v : Except String DateTime) with
    | .localDate d => pure d
    | _ => typeMismatch "a date (YYYY-MM-DD)" v

instance : NotNull DateTime := ⟨⟩
instance : NotNull OffsetDateTime := ⟨⟩
instance : NotNull LocalDateTime := ⟨⟩
instance : NotNull LocalDate := ⟨⟩
instance : NotNull LocalTime := ⟨⟩

instance : ToValue LocalTime := ⟨fun t => .string t.toString⟩
instance : FromValue LocalTime where
  fromValue? v := do
    match ← (fromValue? v : Except String DateTime) with
    | .localTime t => pure t
    | _ => typeMismatch "a time of day (HH:MM:SS)" v

/-! ## Unix time -/

/-- The days from 1970-01-01 to a date (negative before it). -/
def LocalDate.toDaysSinceEpoch (d : LocalDate) : Int :=
  -- Howard Hinnant's `days_from_civil`.
  let y : Int := (d.year : Int) - (if d.month ≤ 2 then 1 else 0)
  let era := y / 400
  let yoe := y - era * 400
  let m : Int := d.month
  let doy := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + (d.day : Int) - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The date `days` days after 1970-01-01 (proleptic Gregorian), if its year is 0 to 9999. -/
def LocalDate.ofDaysSinceEpoch? (days : Int) : Option LocalDate :=
  -- Howard Hinnant's `civil_from_days`; `/` on `Int` rounds down for a positive divisor.
  let z := days + 719468
  let era := z / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let day := doy - (153 * mp + 2) / 5 + 1
  let month := if mp < 10 then mp + 3 else mp - 9
  let year := yoe + era * 400 + (if month ≤ 2 then 1 else 0)
  if 0 ≤ year && year ≤ 9999 then some { year := year.toNat, month := month.toNat, day := day.toNat }
  else none

/-- The instant `ns` nanoseconds after the Unix epoch, in UTC (offset `Z`), if it falls in the
years 0 to 9999. -/
def OffsetDateTime.ofUnixNanos? (ns : Int) : Option OffsetDateTime := do
  let perDay : Int := 86400 * 1000000000
  let days := ns / perDay
  let rest := (ns - days * perDay).toNat
  let secs := rest / 1000000000
  return { date := ← LocalDate.ofDaysSinceEpoch? days
           time := { hour := secs / 3600, minute := secs / 60 % 60, second := secs % 60,
                     nanosecond := rest % 1000000000 } }

/-- The nanoseconds from the Unix epoch to an instant. A leap second counts as the second after
it, as POSIX time has none. -/
def OffsetDateTime.toUnixNanos (dt : OffsetDateTime) : Int :=
  let secs : Int := dt.date.toDaysSinceEpoch * 86400 + dt.time.hour * 3600 +
    dt.time.minute * 60 + dt.time.second - dt.offsetMinutes * 60
  secs * 1000000000 + dt.time.nanosecond

/-- The current time, in UTC. -/
def OffsetDateTime.now : IO OffsetDateTime := do
  let ns := (← Std.Time.Timestamp.now).toNanosecondsSinceUnixEpoch.val
  match OffsetDateTime.ofUnixNanos? ns with
  | some dt => return dt
  | none => throw (IO.userError s!"the clock reads {ns} ns after 1970, outside the years 0 to 9999")

end ExactJSON
