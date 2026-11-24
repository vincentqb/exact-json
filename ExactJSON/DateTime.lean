module

public import ExactJSON.Codec
public import ExactJSON.Calendar

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
  if h : LocalDate.Valid year month day then some (⟨year, month, day, h⟩, cs) else none

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
  if h : LocalTime.Valid hour minute second nanosecond then some (⟨hour, minute, second, nanosecond, h⟩, cs)
  else none

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
      | some (o, []) => if h : o.natAbs < 24 * 60 then some (.offsetDateTime ⟨d, t, o, h⟩) else none
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

instance : NotNull DateTime := ⟨fun _ h => nomatch h⟩
instance : NotNull OffsetDateTime := ⟨fun _ h => nomatch h⟩
instance : NotNull LocalDateTime := ⟨fun _ h => nomatch h⟩
instance : NotNull LocalDate := ⟨fun _ h => nomatch h⟩
instance : NotNull LocalTime := ⟨fun _ h => nomatch h⟩

end ExactJSON
