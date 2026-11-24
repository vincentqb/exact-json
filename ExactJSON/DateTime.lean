module

public import ExactJSON.Codec
public import ExactJSON.Calendar
public import Std.Time.DateTime.Timestamp
import Std.Time.Zoned

@[expose] public section

namespace ExactJSON

protected def LocalDate.toString (d : LocalDate) : String :=
  s!"{Calendar.pad 4 d.year}-{Calendar.pad 2 d.month}-{Calendar.pad 2 d.day}"

protected def LocalTime.toString (t : LocalTime) : String :=
  let base := s!"{Calendar.pad 2 t.hour}:{Calendar.pad 2 t.minute}:{Calendar.pad 2 t.second}"
  if t.nanosecond == 0 then base
  else if t.nanosecond ≥ 1000000000 then s!"{base} (nanosecond {t.nanosecond} out of range)"
  else
    let digits := (Calendar.pad 9 t.nanosecond).toList.reverse.dropWhile (· == '0') |>.reverse
    base ++ "." ++ String.ofList digits

protected def LocalDateTime.toString (dt : LocalDateTime) : String :=
  s!"{dt.date.toString}T{dt.time.toString}"

def offsetText (minutes : Int) : String :=
  if minutes == 0 then "Z"
  else
    let sign := if minutes < 0 then "-" else "+"
    let m := minutes.natAbs
    s!"{sign}{Calendar.pad 2 (m / 60)}:{Calendar.pad 2 (m % 60)}"

protected def OffsetDateTime.toString (dt : OffsetDateTime) : String :=
  s!"{dt.date.toString}T{dt.time.toString}{offsetText dt.offsetMinutes}"

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

namespace DateText

def fixed (n : Nat) (cs : List Char) : Option (Nat × List Char) :=
  let ds := cs.take n
  if ds.length == n && ds.all Char.isDigit then
    some (ds.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0, cs.drop n)
  else none

def lit (c : Char) : List Char → Option (List Char)
  | d :: rest => if c == d then some rest else none
  | [] => none

def date (cs : List Char) : Option (LocalDate × List Char) := do
  let (year, cs) ← fixed 4 cs
  let cs ← lit '-' cs
  let (month, cs) ← fixed 2 cs
  let cs ← lit '-' cs
  let (day, cs) ← fixed 2 cs
  let d : LocalDate := { year, month, day }
  if d.isValid then some (d, cs) else none

def time (cs : List Char) : Option (LocalTime × List Char) := do
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

def offset (cs : List Char) : Option (Int × List Char) :=
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

def shape (s : String) : Option DateTime :=
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

def DateTime.parse? (s : String) : Option DateTime :=
  (DateText.shape s).filter (·.toString == s)

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


instance : ToValue LocalTime := ⟨fun t => .string t.toString⟩
instance : FromValue LocalTime where
  fromValue? v := do
    match ← (fromValue? v : Except String DateTime) with
    | .localTime t => pure t
    | _ => typeMismatch "a time of day (HH:MM:SS)" v

def LocalDate.toDaysSinceEpoch (d : LocalDate) : Int :=
  let y : Int := (d.year : Int) - (if d.month ≤ 2 then 1 else 0)
  let era := y / 400
  let yoe := y - era * 400
  let m : Int := d.month
  let doy := (153 * (if m > 2 then m - 3 else m + 9) + 2) / 5 + (d.day : Int) - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

def LocalDate.ofDaysSinceEpoch? (days : Int) : Option LocalDate :=
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

def OffsetDateTime.ofUnixNanos? (ns : Int) : Option OffsetDateTime := do
  let perDay : Int := 86400 * 1000000000
  let days := ns / perDay
  let rest := (ns - days * perDay).toNat
  let secs := rest / 1000000000
  return { date := ← LocalDate.ofDaysSinceEpoch? days
           time := { hour := secs / 3600, minute := secs / 60 % 60, second := secs % 60,
                     nanosecond := rest % 1000000000 } }

def OffsetDateTime.toUnixNanos (dt : OffsetDateTime) : Int :=
  let secs : Int := dt.date.toDaysSinceEpoch * 86400 + dt.time.hour * 3600 +
    dt.time.minute * 60 + dt.time.second - dt.offsetMinutes * 60
  secs * 1000000000 + dt.time.nanosecond

def OffsetDateTime.now : IO OffsetDateTime := do
  let ns := (← Std.Time.Timestamp.now).toNanosecondsSinceUnixEpoch.val
  match OffsetDateTime.ofUnixNanos? ns with
  | some dt => return dt
  | none => throw (IO.userError s!"the clock reads {ns} ns after 1970, outside the years 0 to 9999")

end ExactJSON
