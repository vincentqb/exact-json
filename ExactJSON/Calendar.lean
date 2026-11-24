module

public import ExactJSON.Value

@[expose] public section

namespace ExactJSON

def isLeapYear (y : Nat) : Bool := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)

def daysInMonth (y m : Nat) : Nat :=
  if m == 2 then (if isLeapYear y then 29 else 28)
  else if m == 4 || m == 6 || m == 9 || m == 11 then 30 else 31

def LocalDate.Valid (year month day : Nat) : Prop :=
  year ≤ 9999 ∧ 1 ≤ month ∧ month ≤ 12 ∧ 1 ≤ day ∧ day ≤ daysInMonth year month

instance (year month day : Nat) : Decidable (LocalDate.Valid year month day) :=
  inferInstanceAs (Decidable (_ ∧ _))

def LocalTime.Valid (hour minute second nanosecond : Nat) : Prop :=
  hour ≤ 23 ∧ minute ≤ 59 ∧ second ≤ 60 ∧ nanosecond < 1000000000

instance (hour minute second nanosecond : Nat) : Decidable (LocalTime.Valid hour minute second nanosecond) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure LocalDate where
  year : Nat
  month : Nat
  day : Nat
  valid : LocalDate.Valid year month day := by decide
  deriving DecidableEq, Repr

structure LocalTime where
  hour : Nat
  minute : Nat
  second : Nat
  nanosecond : Nat := 0
  valid : LocalTime.Valid hour minute second nanosecond := by decide
  deriving DecidableEq, Repr

structure LocalDateTime where
  date : LocalDate
  time : LocalTime
  deriving DecidableEq, Repr

structure OffsetDateTime where
  date : LocalDate
  time : LocalTime
  offsetMinutes : Int := 0
  valid : offsetMinutes.natAbs < 24 * 60 := by decide
  deriving DecidableEq, Repr

inductive DateTime where
  | offsetDateTime (dt : OffsetDateTime)
  | localDateTime (dt : LocalDateTime)
  | localDate (d : LocalDate)
  | localTime (t : LocalTime)
  deriving DecidableEq, Repr

instance : Inhabited LocalDate := ⟨{ year := 1970, month := 1, day := 1 }⟩
instance : Inhabited LocalTime := ⟨{ hour := 0, minute := 0, second := 0 }⟩
instance : Inhabited LocalDateTime := ⟨{ date := default, time := default }⟩
instance : Inhabited OffsetDateTime := ⟨{ date := default, time := default }⟩
instance : Inhabited DateTime := ⟨.localDate default⟩

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

end ExactJSON
