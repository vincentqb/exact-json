module

public import ExactJSON.Value

@[expose] public section

namespace ExactJSON

structure LocalDate where
  year : Nat
  month : Nat
  day : Nat
  deriving DecidableEq, Ord, Repr, Inhabited

structure LocalTime where
  hour : Nat
  minute : Nat
  second : Nat
  nanosecond : Nat := 0
  deriving DecidableEq, Ord, Repr, Inhabited

structure LocalDateTime where
  date : LocalDate
  time : LocalTime
  deriving DecidableEq, Ord, Repr, Inhabited

structure OffsetDateTime where
  date : LocalDate
  time : LocalTime
  offsetMinutes : Int := 0
  deriving DecidableEq, Repr, Inhabited

inductive DateTime where
  | offsetDateTime (dt : OffsetDateTime)
  | localDateTime (dt : LocalDateTime)
  | localDate (d : LocalDate)
  | localTime (t : LocalTime)
  deriving DecidableEq, Repr, Inhabited

def isLeapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysInMonth (y m : Nat) : Nat :=
  if m == 2 then (if isLeapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

def LocalDate.isValid (d : LocalDate) : Bool :=
  d.year ≤ 9999 && 1 ≤ d.month && d.month ≤ 12 && 1 ≤ d.day && d.day ≤ daysInMonth d.year d.month

def LocalTime.isValid (t : LocalTime) : Bool :=
  t.hour ≤ 23 && t.minute ≤ 59 && t.second ≤ 60 && t.nanosecond < 1000000000

def LocalDateTime.isValid (dt : LocalDateTime) : Bool := dt.date.isValid && dt.time.isValid

def OffsetDateTime.isValid (dt : OffsetDateTime) : Bool :=
  dt.date.isValid && dt.time.isValid && dt.offsetMinutes.natAbs < 24 * 60

def DateTime.isValid : DateTime → Bool
  | .offsetDateTime dt => dt.isValid
  | .localDateTime dt => dt.isValid
  | .localDate d => d.isValid
  | .localTime t => t.isValid

namespace Calendar

def pad (width n : Nat) : String :=
  String.ofList (List.replicate (width - (Nat.toDigits 10 n).length) '0' ++ Nat.toDigits 10 n)

def fraction (nanosecond : Nat) : String :=
  if nanosecond = 0 then "" else "." ++ String.ofList ((pad 9 nanosecond).toList.reverse.dropWhile (· = '0')).reverse

def offset (minutes : Int) : String :=
  if minutes = 0 then "Z"
  else (if minutes < 0 then "-" else "+") ++ pad 2 (minutes.natAbs / 60) ++ ":" ++ pad 2 (minutes.natAbs % 60)

end Calendar

def LocalDate.text (d : LocalDate) : String :=
  Calendar.pad 4 d.year ++ "-" ++ Calendar.pad 2 d.month ++ "-" ++ Calendar.pad 2 d.day

def LocalTime.text (t : LocalTime) : String :=
  Calendar.pad 2 t.hour ++ ":" ++ Calendar.pad 2 t.minute ++ ":" ++ Calendar.pad 2 t.second ++ Calendar.fraction t.nanosecond

def LocalDateTime.text (dt : LocalDateTime) : String := dt.date.text ++ "T" ++ dt.time.text

def OffsetDateTime.text (dt : OffsetDateTime) : String :=
  dt.date.text ++ "T" ++ dt.time.text ++ Calendar.offset dt.offsetMinutes

def DateTime.text : DateTime → String
  | .offsetDateTime dt => dt.text
  | .localDateTime dt => dt.text
  | .localDate d => d.text
  | .localTime t => t.text

instance : NotNull DateTime := ⟨⟩
instance : NotNull OffsetDateTime := ⟨⟩
instance : NotNull LocalDateTime := ⟨⟩
instance : NotNull LocalDate := ⟨⟩
instance : NotNull LocalTime := ⟨⟩

end ExactJSON
