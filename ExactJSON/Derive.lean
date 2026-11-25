module

public import ExactJSON.Codec
public meta import Lean.Elab.Deriving.Basic
public meta import Lean.Elab.Deriving.Util

@[expose] public section

namespace ExactJSON.Derive

universe u


def present : List (String × Bool) → List (Option Value) → List (String × Value)
  | (k, _) :: schema, some v :: es => (k, v) :: present schema es
  | _ :: schema, none :: es => present schema es
  | _, _ => []

def record (schema : List (String × Bool)) (es : List (Option Value)) : Value := .table ⟨present schema es⟩

def slots (name : String) : List (String × Bool) → List (String × Value) → Except String (List (Option Value))
  | [], [] => .ok []
  | [], (k, _) :: _ => .error s!"{name} has no field {pushString "" k}"
  | (key, optional) :: schema, (k, v) :: rest =>
    if k == key then (some v :: ·) <$> slots name schema rest
    else if optional then (none :: ·) <$> slots name schema ((k, v) :: rest)
    else if k < key then .error s!"{name} has no field {pushString "" k}"
    else .error s!"missing key {pushString "" key}"
  | (key, optional) :: schema, [] =>
    if optional then (none :: ·) <$> slots name schema [] else .error s!"missing key {pushString "" key}"

def fields (name : String) (schema : List (String × Bool)) : Value → Except String (List (Option Value))
  | .table ⟨ms⟩ => slots name schema ms
  | v => typeMismatch s!"a table ({name})" v

def req {α : Type u} (read : Value → Except String α) (key : String) : Option Value → Except String α
  | some v => withContext key (read v)
  | none => .error s!"missing key {key}"

def opt {α : Type u} (read : Value → Except String α) (key : String) : Option Value → Except String (Option α)
  | some v => some <$> withContext key (read v)
  | none => .ok none

def ofTag : String × Option Value → Value
  | (name, none) => .string name
  | (name, some p) => .table #[(name, p)]

def tag? : Value → Except String (String × Option Value)
  | .string s => .ok (s, none)
  | .table #[(k, p)] => .ok (k, some p)
  | v => typeMismatch "a constructor: its name, or a table of one key" v

def codesLt : List Nat → List Nat → Bool
  | [], _ :: _ => true
  | a :: as, b :: bs => if Nat.blt a b then true else if Nat.beq a b then codesLt as bs else false
  | _, _ => false

theorem lt_of_codesLt : ∀ {l₁ l₂ : List Char}, codesLt (l₁.map Char.toNat) (l₂.map Char.toNat) = true → l₁ < l₂
  | [], _ :: _, _ => List.Lex.nil
  | a :: as, b :: bs, h => by
    simp only [List.map_cons, codesLt] at h
    by_cases hab : Nat.blt a.toNat b.toNat = true
    · exact List.Lex.rel (by simpa [Nat.blt_eq, Char.lt_def, UInt32.lt_iff_toNat_lt] using hab)
    · simp only [hab, Bool.false_eq_true, ite_false] at h
      by_cases he : Nat.beq a.toNat b.toNat = true
      · simp only [he, ite_true] at h
        have : a = b := Char.ext (UInt32.toNat_inj.mp (by simpa using he))
        subst this
        exact List.Lex.cons (lt_of_codesLt h)
      · simp [he] at h
  | [], [], h => by simp [codesLt] at h
  | _ :: _, [], h => by simp [codesLt] at h

theorem string_lt {l₁ l₂ : List Char} (h : codesLt (l₁.map Char.toNat) (l₂.map Char.toNat) = true) :
    String.ofList l₁ < String.ofList l₂ :=
  String.toList_lt_toList_iff.mp (by rw [String.toList_ofList, String.toList_ofList]; exact lt_of_codesLt h)

theorem keysIncreaseFrom_nil {a : String} : keysIncreaseFrom a [] = true := rfl

theorem keysIncreaseFrom_cons {a b : String} {rest : List String} (h : a < b) (t : keysIncreaseFrom b rest = true) :
    keysIncreaseFrom a (b :: rest) = true := by
  simp only [keysIncreaseFrom, decide_eq_true h, t, Bool.and_self]

theorem keysIncrease_nil : keysIncrease [] = true := rfl

theorem keysIncrease_cons {a : String} {rest : List String} (h : keysIncreaseFrom a rest = true) :
    keysIncrease (a :: rest) = true := h

inductive Fits : List (String × Bool) → List (Option Value) → Prop
  | nil : Fits [] []
  | req {k : String} {v : Value} {s es} : Fits s es → Fits ((k, false) :: s) (some v :: es)
  | opt {k : String} {o : Option Value} {s es} : Fits s es → Fits ((k, true) :: s) (o :: es)

def Above (key : String) (schema : List (String × Bool)) : Prop := ∀ p ∈ schema, key < p.1

theorem above_of_increase {key : String} {schema : List (String × Bool)}
    (h : keysIncreaseFrom key (schema.map (·.1)) = true) : Above key schema := by
  induction schema generalizing key with
  | nil => intro p hp; cases hp
  | cons q rest ih =>
    simp only [List.map, keysIncreaseFrom, Bool.and_eq_true, decide_eq_true_eq] at h
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact h.1
    · exact Std.lt_trans h.1 (ih h.2 p hp)

theorem present_above {key : String} {schema es} (h : Above key schema) : ∀ p ∈ present schema es, key < p.1 := by
  induction schema generalizing es with
  | nil => cases es <;> simp [present]
  | cons q rest ih =>
    obtain ⟨k, b⟩ := q
    have hk : key < k := h (k, b) (List.mem_cons_self ..)
    have hr : Above key rest := fun p hp => h p (List.mem_cons_of_mem _ hp)
    cases es with
    | nil => simp [present]
    | cons e es =>
      cases e with
      | none => exact ih hr
      | some v =>
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hk
        · exact ih hr p hp

theorem slots_present_none {name : String} {key : String} {schema : List (String × Bool)} {es}
    (hrest : ∀ p ∈ present schema es, key < p.1) (ih : slots name schema (present schema es) = .ok es) :
    slots name ((key, true) :: schema) (present schema es) = .ok (none :: es) := by
  generalize hl : present schema es = l at hrest ih
  cases l with
  | nil => simp [slots, ih, Functor.map, Except.map]
  | cons p rest =>
    obtain ⟨k, v⟩ := p
    have hk : key < k := hrest (k, v) (List.mem_cons_self ..)
    have hne : (k == key) = false := by
      rw [beq_eq_false_iff_ne]; intro h; subst h; exact Std.lt_irrefl hk
    simp [slots, hne, ih, Functor.map, Except.map]

theorem slots_present {name : String} {schema : List (String × Bool)} {es : List (Option Value)}
    (hsorted : keysIncrease (schema.map (·.1)) = true) (hfit : Fits schema es) :
    slots name schema (present schema es) = .ok es := by
  induction hfit with
  | nil => rfl
  | @req k v s es _ ih =>
    have hs : keysIncrease (s.map (·.1)) = true := by
      cases s with
      | nil => rfl
      | cons q rest => simp only [List.map, keysIncrease, keysIncreaseFrom, Bool.and_eq_true] at hsorted ⊢; exact hsorted.2
    simp [present, slots, ih hs, Functor.map, Except.map]
  | @opt k o s es _ ih =>
    have hs : keysIncrease (s.map (·.1)) = true := by
      cases s with
      | nil => rfl
      | cons q rest => simp only [List.map, keysIncrease, keysIncreaseFrom, Bool.and_eq_true] at hsorted ⊢; exact hsorted.2
    have habove : Above k s := above_of_increase (by simpa [keysIncrease] using hsorted)
    cases o with
    | none => exact slots_present_none (present_above habove) (ih hs)
    | some v => simp [present, slots, ih hs, Functor.map, Except.map]

theorem fields_record {name : String} {schema : List (String × Bool)} {es : List (Option Value)}
    (hsorted : keysIncrease (schema.map (·.1)) = true) (hfit : Fits schema es) :
    fields name schema (record schema es) = .ok es :=
  slots_present hsorted hfit

theorem req_some {α : Type u} {read : Value → Except String α} {key : String} {v : Value} {a : α}
    (h : read v = .ok a) : req read key (some v) = .ok a := by
  simp [req, h, withContext, Except.mapError]

theorem opt_map {α : Type u} [ToValue α] {read : Value → Except String α} {key : String}
    (h : ∀ a : α, read (toValue a) = .ok a) (o : Option α) : opt read key (o.map toValue) = .ok o := by
  cases o <;> simp [opt, h, withContext, Except.mapError, Functor.map, Except.map]

theorem tag?_ofTag (t : String × Option Value) : tag? (ofTag t) = .ok t := by
  obtain ⟨n, _ | p⟩ := t <;> rfl

mutual
def depth : Value → Nat
  | .array ⟨items⟩ => depthItems items + 1
  | .table ⟨members⟩ => depthMembers members + 1
  | _ => 0
def depthItems : List Value → Nat
  | [] => 0
  | v :: rest => max (depth v) (depthItems rest)
def depthMembers : List (String × Value) → Nat
  | [] => 0
  | (_, v) :: rest => max (depth v) (depthMembers rest)
end

def fuel {α : Type u} (step : (Value → Except String α) → Value → Except String α) :
    Nat → Value → Except String α
  | 0, _ => .error "decoding recursed deeper than the value"
  | n + 1, v => step (fuel step n) v

def fix {α : Type u} (step : (Value → Except String α) → Value → Except String α) (v : Value) :
    Except String α :=
  fuel step (depth v + 1) v

theorem fuel_ok {α : Type u} (step : (Value → Except String α) → Value → Except String α)
    (enc : α → Value)
    (hstep : ∀ (decode : Value → Except String α) (a : α),
      (∀ b, depth (enc b) < depth (enc a) → decode (enc b) = .ok b) → step decode (enc a) = .ok a) :
    ∀ n a, depth (enc a) < n → fuel step n (enc a) = .ok a := by
  intro n
  induction n with
  | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih => exact fun a h => hstep _ a fun b hb => ih b (by omega)

theorem fix_ok {α : Type u} (step : (Value → Except String α) → Value → Except String α)
    (enc : α → Value)
    (hstep : ∀ (decode : Value → Except String α) (a : α),
      (∀ b, depth (enc b) < depth (enc a) → decode (enc b) = .ok b) → step decode (enc a) = .ok a)
    (a : α) : fix step (enc a) = .ok a :=
  fuel_ok step enc hstep _ a (Nat.lt_succ_self _)

theorem depth_le_items {v : Value} : ∀ {xs : List Value}, v ∈ xs → depth v ≤ depthItems xs
  | _ :: _, .head _ => by simp only [depthItems]; omega
  | _ :: _, .tail _ h => by have := depth_le_items h; simp only [depthItems]; omega

theorem depth_le_members {v : Value} : ∀ {ms : List (String × Value)} {k : String}, (k, v) ∈ ms → depth v ≤ depthMembers ms
  | _ :: _, _, .head _ => by simp only [depthMembers]; omega
  | (_, _) :: _, _, .tail _ h => by have := depth_le_members h; simp only [depthMembers]; omega

theorem mem_present {v : Value} : ∀ {schema : List (String × Bool)} {es : List (Option Value)},
    Fits schema es → some v ∈ es → ∃ k, (k, v) ∈ present schema es
  | _, _, .nil, h => by cases h
  | _, _, @Fits.req k w s es hf, h => by
    rcases List.mem_cons.mp h with h | h
    · cases h; exact ⟨k, List.mem_cons_self ..⟩
    · obtain ⟨k', hk⟩ := mem_present hf h; exact ⟨k', List.mem_cons_of_mem _ hk⟩
  | _, _, @Fits.opt k o s es hf, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; exact ⟨k, List.mem_cons_self ..⟩
    · obtain ⟨k', hk⟩ := mem_present hf h
      cases o with
      | none => exact ⟨k', hk⟩
      | some w => exact ⟨k', List.mem_cons_of_mem _ hk⟩

theorem depth_ofTag_record {n : String} {schema : List (String × Bool)} {es : List (Option Value)} {v : Value}
    (hfit : Fits schema es) (hmem : some v ∈ es) : depth v < depth (ofTag (n, some (record schema es))) := by
  obtain ⟨k, hk⟩ := mem_present hfit hmem
  have := depth_le_members hk
  simp only [ofTag, record, depth, depthMembers, List.toArray]
  omega

theorem depth_ofTag_array {n : String} {xs : List Value} {v : Value} (hmem : v ∈ xs) :
    depth v < depth (ofTag (n, some (.array ⟨xs⟩))) := by
  have := depth_le_items hmem
  simp only [ofTag, depth, depthMembers]
  omega

theorem depth_ofTag_some {n : String} {v : Value} : depth v < depth (ofTag (n, some v)) := by
  simp only [ofTag, depth, depthMembers]
  omega

inductive AllValid : List (Option Value) → Prop
  | nil : AllValid []
  | some {v : Value} {es} : v.Valid → AllValid es → AllValid (some v :: es)
  | none {es} : AllValid es → AllValid (none :: es)

theorem AllValid.map {α : Type u} [ToValue α] {es} (h : ∀ a : α, (toValue a).Valid) (o : Option α)
    (t : AllValid es) : AllValid (o.map toValue :: es) := by
  cases o with
  | none => exact .none t
  | some a => exact .some (h a) t

theorem keysIncreaseFrom_iff (k : String) (l : List String) :
    keysIncreaseFrom k l = true ↔ (k :: l).Pairwise (· < ·) := by
  induction l generalizing k with
  | nil => simp [keysIncreaseFrom]
  | cons x rest ih =>
    simp only [keysIncreaseFrom, Bool.and_eq_true, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨hx, hp⟩
      refine List.Pairwise.cons ?_ hp
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact Std.lt_trans hx (List.rel_of_pairwise_cons hp hy)
    · intro h
      exact ⟨List.rel_of_pairwise_cons h (List.mem_cons_self ..), h.of_cons⟩

theorem keysIncrease_iff (l : List String) : keysIncrease l = true ↔ l.Pairwise (· < ·) := by
  cases l with
  | nil => simp [keysIncrease]
  | cons k rest => exact keysIncreaseFrom_iff k rest

theorem present_keys_sublist : ∀ {schema : List (String × Bool)} {es : List (Option Value)},
    ((present schema es).map (·.1)).Sublist (schema.map (·.1))
  | [], _ => by simp [present]
  | (k, b) :: s, [] => by simp [present]
  | (k, b) :: s, some v :: es => by simpa [present] using present_keys_sublist (schema := s) (es := es)
  | (k, b) :: s, none :: es => by
    simpa [present] using (present_keys_sublist (schema := s) (es := es)).cons k

theorem membersValid_present : ∀ {schema : List (String × Bool)} {es : List (Option Value)},
    AllValid es → membersValid (present schema es) = true
  | [], _, _ => by simp [present, membersValid]
  | (k, b) :: s, [], _ => by simp [present, membersValid]
  | (k, b) :: s, some v :: es, .some hv t => by simp [present, membersValid, hv, membersValid_present (schema := s) t]
  | (k, b) :: s, none :: es, .none t => by simpa [present] using membersValid_present (schema := s) t

theorem valid_record {schema : List (String × Bool)} {es : List (Option Value)}
    (hsorted : keysIncrease (schema.map (·.1)) = true) (hv : AllValid es) : (record schema es).Valid := by
  have hp := ((keysIncrease_iff _).mp hsorted).sublist (present_keys_sublist (schema := schema) (es := es))
  simp only [Value.Valid, record, Value.isValid, Bool.and_eq_true]
  exact ⟨(keysIncrease_iff _).mpr hp, membersValid_present hv⟩

theorem valid_ofTag_none {n : String} : (ofTag (n, none)).Valid := rfl

theorem valid_ofTag_some {n : String} {v : Value} (h : v.Valid) : (ofTag (n, some v)).Valid := by
  simp only [Value.Valid, ofTag, Value.isValid, keysIncrease, keysIncreaseFrom, membersValid, h, Bool.and_true, List.map]

theorem valid_array {xs : List Value} (h : itemsValid xs = true) : (Value.array ⟨xs⟩).Valid := h

theorem itemsValid_cons {v : Value} {xs : List Value} (h : v.Valid) (t : itemsValid xs = true) :
    itemsValid (v :: xs) = true := by simp [itemsValid, h, t]

theorem record_ne_null {schema : List (String × Bool)} {es : List (Option Value)} : record schema es ≠ .null := nofun

theorem ofTag_ne_null (t : String × Option Value) : ofTag t ≠ .null := by
  obtain ⟨n, _ | p⟩ := t <;> nofun

theorem valid_of_depth {α : Type u} (enc : α → Value)
    (h : ∀ a, (∀ b, depth (enc b) < depth (enc a) → (enc b).Valid) → (enc a).Valid) : ∀ a, (enc a).Valid := by
  suffices ∀ n a, depth (enc a) < n → (enc a).Valid from fun a => this _ a (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih => exact fun a ha => h a fun b hb => ih b (by omega)

def Rd (β : Type u) : Type u := List (Option Value) → Except String (β × List (Option Value))

@[inline] def Rd.pure {β : Type u} (b : β) : Rd β := fun es => .ok (b, es)

@[inline] def Rd.ap {α β : Type u} (f : Rd (α → β)) (read : Option Value → Except String α) : Rd β := fun es =>
  match f es with
  | .ok (g, e :: rest) =>
    match read e with
    | .ok a => .ok (g a, rest)
    | .error err => .error err
  | .ok (_, []) => .error "fewer fields than expected"
  | .error err => .error err

def decodeFields {β : Type u} (name : String) (schema : List (String × Bool)) (r : Rd β) (v : Value) :
    Except String β :=
  match fields name schema v with
  | .ok es =>
    match r es with
    | .ok (b, _) => .ok b
    | .error err => .error err
  | .error err => .error err

def Reads {β : Type u} (r : Rd β) (es : List (Option Value)) (b : β) (rest : List (Option Value)) : Prop :=
  r es = .ok (b, rest)

theorem Reads.pure {β : Type u} {b : β} {es : List (Option Value)} : Reads (Rd.pure b) es b es := rfl

theorem Reads.ap {α β : Type u} {f : Rd (α → β)} {read : Option Value → Except String α} {es rest : List (Option Value)}
    {g : α → β} {e : Option Value} {a : α} (hf : Reads f es g (e :: rest)) (hr : read e = .ok a) :
    Reads (Rd.ap f read) es (g a) rest := by
  unfold Reads at hf ⊢
  simp only [Rd.ap, hf, hr]

theorem decodeFields_record {β : Type u} {name : String} {schema : List (String × Bool)} {es : List (Option Value)}
    {r : Rd β} {b : β} {rest : List (Option Value)}
    (hsorted : keysIncrease (schema.map (·.1)) = true) (hfit : Fits schema es) (h : Reads r es b rest) :
    decodeFields name schema r (record schema es) = .ok b := by
  unfold Reads at h
  simp only [decodeFields, fields_record hsorted hfit, h]

def dispatch {α : Type u} (tag : String) (p : Option Value) :
    List (String × (Option Value → Except String α)) → Except String α
  | [] => .error s!"unknown constructor {pushString "" tag}"
  | (k, alt) :: rest => if k == tag then alt p else dispatch tag p rest

def decodeTagged {α : Type u} (alts : List (String × (Option Value → Except String α))) (v : Value) :
    Except String α :=
  match tag? v with
  | .ok (tag, p) => dispatch tag p alts
  | .error e => .error e

def noArgs {α : Type u} (name : String) (c : α) : Option Value → Except String α
  | none => .ok c
  | some _ => .error s!"constructor {name} takes no arguments"

def withPayload {α : Type u} (name : String) (f : Value → Except String α) : Option Value → Except String α
  | some p => withContext name (f p)
  | none => .error s!"constructor {name} takes arguments"

def decodeItems {β : Type u} (name : String) (n : Nat) (r : Rd β) : Value → Except String β
  | .array ⟨xs⟩ =>
    if xs.length = n then
      match r (xs.map some) with
      | .ok (b, _) => .ok b
      | .error err => .error err
    else typeMismatch s!"an array of {n} items ({name})" (.array ⟨xs⟩)
  | v => typeMismatch s!"an array of {n} items ({name})" v

theorem dispatch_of_mem {α : Type u} {tag : String} {p : Option Value} :
    ∀ {alts : List (String × (Option Value → Except String α))} {alt},
      (alts.map (·.1)).Nodup → (tag, alt) ∈ alts → dispatch tag p alts = alt p
  | (k, f) :: rest, alt, hnd, hmem => by
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hmem with h | h
    · cases h; simp [dispatch]
    · have hk : k ≠ tag := fun hk => hnd.1 (hk ▸ List.mem_map_of_mem (f := (·.1)) h)
      simp only [dispatch, beq_iff_eq, hk, ite_false]
      exact dispatch_of_mem hnd.2 h

theorem decodeTagged_ofTag {α : Type u} {alts : List (String × (Option Value → Except String α))} {n : String}
    {p : Option Value} {alt} (hnd : (alts.map (·.1)).Nodup) (hmem : (n, alt) ∈ alts) :
    decodeTagged alts (ofTag (n, p)) = alt p := by
  simp only [decodeTagged, tag?_ofTag]
  exact dispatch_of_mem hnd hmem

theorem nodup_of_increase {l : List String} (h : keysIncrease l = true) : l.Nodup :=
  List.Pairwise.imp (R := (· < ·)) (fun {a b} (hab : a < b) (heq : a = b) => by subst heq; exact Std.lt_irrefl hab) ((keysIncrease_iff l).mp h)

theorem withPayload_fields {β : Type u} {name : String} {schema : List (String × Bool)} {es : List (Option Value)}
    {r : Rd β} {b : β} {rest : List (Option Value)}
    (hsorted : keysIncrease (schema.map (·.1)) = true) (hfit : Fits schema es) (h : Reads r es b rest) :
    withPayload name (decodeFields name schema r) (some (record schema es)) = .ok b := by
  simp only [withPayload, decodeFields_record hsorted hfit h]; rfl

theorem withPayload_map {α β : Type u} {name : String} {read : Value → Except String α} {f : α → β} {v : Value} {a : α}
    (h : read v = .ok a) : withPayload name (fun p => f <$> read p) (some v) = .ok (f a) := by
  simp only [withPayload, h]; rfl

theorem withPayload_items {β : Type u} {name : String} {n : Nat} {xs : List Value} {r : Rd β} {b : β}
    {rest : List (Option Value)} (hlen : xs.length = n) (h : Reads r (xs.map some) b rest) :
    withPayload name (decodeItems name n r) (some (.array ⟨xs⟩)) = .ok b := by
  unfold Reads at h
  simp only [withPayload, decodeItems, hlen, ite_true, h]; rfl


theorem noArgs_none {α : Type u} {name : String} {c : α} : noArgs name c none = .ok c := rfl

theorem itemsValid_nil : itemsValid [] = true := rfl

end ExactJSON.Derive

end

public meta section

namespace ExactJSON.Derive
open Lean Elab Command Term Meta Parser.Term Lean.Elab.Deriving

inductive Shape where
  | noArgs
  | single
  | positional
  | named
  deriving Inhabited

structure Fld where
  name : Name
  key : String
  optional : Bool
  recursive : Bool
  deriving Inhabited

structure Ctor where
  name : Name
  tag : String
  shape : Shape
  fields : Array Fld
  numParams : Nat
  deriving Inhabited

def fieldKey (n : Name) : CoreM String := do
  let .str .anonymous s := n.eraseMacroScopes | throwError "invalid field name {n}"
  return (s.dropEndWhile (· == '?')).copy

def checkKeys (fields : Array Fld) : CoreM Unit := do
  for i in [0:fields.size] do
    for j in [i + 1:fields.size] do
      if fields[i]!.key == fields[j]!.key then
        throwError "`{fields[i]!.name}` and `{fields[j]!.name}` would both be written under the key {repr fields[i]!.key}"

def checkType (indVal : InductiveVal) : MetaM Unit := do
  if indVal.all.length > 1 then
    throwError "deriving ExactJSON instances for mutual inductive types is not supported"
  if indVal.isNested then
    throwError "deriving ExactJSON instances for nested inductive types is not supported: a constructor holds `{privateToUserName indVal.name}` inside another type"
  if indVal.numIndices > 0 then
    throwError "deriving ExactJSON instances for indexed families is not supported"
  if isStructure (← getEnv) indVal.name && indVal.isRec then
    throwError "deriving ExactJSON instances for recursive structures is not supported"

def checkField (indVal : InductiveVal) (name : Name) (type : Expr) (earlier : Array Expr) : MetaM (Bool × Bool) := do
  if ← isProp type then
    throwError "field `{name}` is a proof, which JSON does not hold"
  if earlier.any fun x => type.containsFVar x.fvarId! then
    throwError "the type of field `{name}` depends on another field"
  let type := type.consumeMData
  let recursive := type.isAppOf indVal.name
  if !recursive && (type.find? (·.isConstOf indVal.name)).isSome then
    throwError "field `{name}` holds `{privateToUserName indVal.name}` other than as itself"
  return (type.isAppOfArity ``Option 1, recursive)

def structFields (indVal : InductiveVal) : MetaM (Array Fld) := do
  let names := getStructureFieldsFlattened (← getEnv) indVal.name (includeSubobjectFields := false)
  forallBoundedTelescope indVal.type indVal.numParams fun params _ => do
    withLocalDeclD `x (mkAppN (.const indVal.name (indVal.levelParams.map Level.param)) params) fun x => do
      let mut out := #[]
      for name in names do
        let type ← inferType (← mkProjection x name)
        let (optional, _) ← checkField indVal name type #[x]
        out := out.push { name, key := ← fieldKey name, optional, recursive := false }
      checkKeys out
      return out

def ctorsOf (indVal : InductiveVal) : MetaM (Array Ctor) := do
  indVal.ctors.toArray.mapM fun ctorName => do
    let ctorInfo ← getConstInfoCtor ctorName
    forallTelescopeReducing ctorInfo.type fun xs _ => do
      let mut fields := #[]
      let mut named := true
      let mut earlier := #[]
      for i in [0:ctorInfo.numFields] do
        let x := xs[indVal.numParams + i]!
        let decl ← x.fvarId!.getDecl
        let (optional, recursive) ← checkField indVal decl.userName decl.type earlier
        earlier := earlier.push x
        if decl.userName.hasMacroScopes || decl.userName.isAnonymous then named := false
        let key ← if named then fieldKey decl.userName else pure ""
        fields := fields.push { name := decl.userName, key, optional, recursive }
      let shape :=
        if fields.isEmpty then Shape.noArgs
        else if named then Shape.named
        else if fields.size == 1 then Shape.single
        else Shape.positional
      if named then checkKeys fields
      return { name := ctorName, tag := ctorName.eraseMacroScopes.getString!, shape, fields,
               numParams := indVal.numParams }

def sortByKey {α : Type} (xs : Array α) (key : α → String) : Array α :=
  xs.qsort (key · < key ·)

def strLit (s : String) : Term := Syntax.mkStrLit s

def schemaTerm (fields : Array Fld) : TermElabM Term := do
  let elems ← (sortByKey fields (·.key)).mapM fun f => do
    let b ← if f.optional then `(true) else `(false)
    `(($(strLit f.key), $b))
  `([$elems,*])

def memTerm (i : Nat) : TermElabM Term := do
  let mut t ← `(List.Mem.head _)
  for _ in [0:i] do
    t ← `(List.Mem.tail _ $t)
  return t

def keysSortedProof (keys : Array String) : TermElabM Term := do
  if keys.isEmpty then return ← `(ExactJSON.Derive.keysIncrease_nil)
  let mut chain ← `(ExactJSON.Derive.keysIncreaseFrom_nil)
  for _ in [1:keys.size] do
    chain ← `(ExactJSON.Derive.keysIncreaseFrom_cons (ExactJSON.Derive.string_lt rfl) $chain)
  `(ExactJSON.Derive.keysIncrease_cons $chain)

def keysSorted (keys : Array String) : TermElabM Term := do
  let lits := keys.map strLit
  `((show ExactJSON.keysIncrease [$lits,*] = true from $(← keysSortedProof keys)))

def sortedKeys (fields : Array Fld) : Array String := (sortByKey fields (·.key)).map (·.key)

structure Params where
  implicit : Array (TSyntax ``bracketedBinder)
  types : Array Ident
  indType : Term

def params (indVal : InductiveVal) : TermElabM Params := do
  let argNames ← mkInductArgNames indVal
  let implicit ← argNames.mapM fun n => `(bracketedBinderF| {$(mkIdent n)})
  let types ← forallBoundedTelescope indVal.type indVal.numParams fun xs _ => do
    let mut out := #[]
    for h : i in [0:xs.size] do
      try
        let c ← mkAppM ``ToValue #[xs[i]]
        if ← isTypeCorrect c then out := out.push (mkIdent argNames[i]!)
      catch _ => pure ()
    return out
  return { implicit, types, indType := ← mkInductiveApp indVal argNames }

def instBinders (ps : Params) (classes : List Name) : TermElabM (Array (TSyntax ``bracketedBinder)) := do
  let mut out := ps.implicit
  for t in ps.types do
    for c in classes do
      out := out.push (← `(bracketedBinderF| [$(mkCIdent c) $t]))
  return out

def fresh (n : Name) : TermElabM Ident := return mkIdent (← mkFreshUserName n)

def auxName (declName : Name) (suffix : String) : Ident :=
  mkIdent (`exactJSON ++ privateToUserName declName.eraseMacroScopes ++ .mkSimple suffix)

def ctorPattern (indVal : InductiveVal) (ctor : Ctor) (vars : Array Ident) : TermElabM Term := do
  let holes ← (Array.range indVal.numParams).mapM fun _ => `(_)
  `(@$(mkIdent ctor.name):ident $holes:term* $vars:term*)

def entryTerm (auxTo : Ident) (f : Fld) (access : Term) : TermElabM Term :=
  if f.recursive then `(some ($auxTo $access))
  else if f.optional then `(Option.map ExactJSON.toValue $access)
  else `(some (ExactJSON.toValue $access))

def encodeRecord (auxTo : Ident) (fields : Array Fld) (access : Array Term) : TermElabM Term := do
  let order := sortByKey (Array.range fields.size) (fields[·]!.key)
  let entries ← order.mapM fun i => entryTerm auxTo fields[i]! access[i]!
  `(ExactJSON.Derive.record $(← schemaTerm fields) [$entries,*])

def ctorPayload (auxTo : Ident) (ctor : Ctor) (vars : Array Ident) : TermElabM Term := do
  let enc (f : Fld) (x : Ident) : TermElabM Term :=
    if f.recursive then `($auxTo $x) else `(ExactJSON.toValue $x)
  let payload ← match ctor.shape with
    | .noArgs => `(none)
    | .single => `(some $(← enc ctor.fields[0]! vars[0]!))
    | .positional => do
      let items ← (Array.range vars.size).mapM fun i => enc ctor.fields[i]! vars[i]!
      `(some (ExactJSON.Value.array ⟨[$items,*]⟩))
    | .named => do `(some $(← encodeRecord auxTo ctor.fields (vars.map (⟨·.raw⟩))))
  return payload

def encodeCtor (auxTo : Ident) (ctor : Ctor) (vars : Array Ident) : TermElabM Term := do
  `(ExactJSON.Derive.ofTag ($(strLit ctor.tag), $(← ctorPayload auxTo ctor vars)))

def mkToValueCmds (declName : Name) : TermElabM (Array Command) := do
  let indVal ← getConstInfoInduct declName
  checkType indVal
  let ctx ← mkContext ``ToValue "toValue" declName
  let auxTo := auxName declName "toValue"
  let ps ← params indVal
  let binders ← instBinders ps [``ToValue]
  let x ← fresh `x
  let (body, notNull) ← if isStructure (← getEnv) declName then do
      let fields ← structFields indVal
      let access ← fields.mapM fun f => `($x.$(mkIdent f.name):ident)
      pure (← encodeRecord auxTo fields access, ← `(fun _ => ExactJSON.Derive.record_ne_null))
    else do
      let ctors ← ctorsOf indVal
      let mut alts := #[]
      let mut nnAlts := #[]
      for ctor in ctors do
        let vars ← ctor.fields.mapM fun _ => fresh `a
        let pat ← ctorPattern indVal ctor vars
        alts := alts.push (← `(matchAltExpr| | $pat:term => $(← encodeCtor auxTo ctor vars)))
        nnAlts := nnAlts.push (← `(matchAltExpr| | $pat:term =>
          ExactJSON.Derive.ofTag_ne_null ($(strLit ctor.tag), $(← ctorPayload auxTo ctor vars))))
      let a ← fresh `a
      pure (← `(match $x:ident with $alts:matchAlt*), ← `(fun $a => match $a:ident with $nnAlts:matchAlt*))
  let notNullName ← mkInstName ``NotNull declName
  return #[
    ← `(def $auxTo:ident $binders:bracketedBinder* ($x : $(ps.indType)) : ExactJSON.Value := $body),
    ← `(instance $(mkIdent ctx.instName):ident $binders:bracketedBinder* : ExactJSON.ToValue $(ps.indType) := ⟨$auxTo⟩),
    ← `(instance $(mkIdent notNullName):ident $binders:bracketedBinder* : ExactJSON.NotNull $(ps.indType) := ⟨$notNull⟩)]

def readerTerm (fields : Array Fld) (lam : Term) (read : Fld → Term) (useOpt : Bool) (keyOf : Nat → String)
    (order : Array Nat) : TermElabM Term := do
  let mut r ← `(ExactJSON.Derive.Rd.pure $lam)
  for i in order do
    let f := fields[i]!
    let rd ← if useOpt && f.optional then `(ExactJSON.Derive.opt $(read f) $(strLit (keyOf i)))
      else `(ExactJSON.Derive.req $(read f) $(strLit (keyOf i)))
    r ← `(ExactJSON.Derive.Rd.ap $r $rd)
  return r

def keyOrder (fields : Array Fld) : Array Nat := sortByKey (Array.range fields.size) (fields[·]!.key)

def structLambda (fields : Array Fld) (indType : Term) : TermElabM Term := do
  if fields.isEmpty then return ← `((⟨⟩ : $indType))
  let order := keyOrder fields
  let ys ← fields.mapM fun _ => fresh `y
  let names := fields.map (mkIdent ·.name)
  let sortedYs := order.map (ys[·]!)
  `(fun $sortedYs:ident* => ({ $[$names:ident := $ys],* } : $indType))

def ctorApp (ctor : Ctor) (args : Array Term) : TermElabM Term := do
  let holes ← (Array.range ctor.numParams).mapM fun _ => `(_)
  `(@$(mkIdent ctor.name):ident $holes:term* $args:term*)

def ctorLambda (ctor : Ctor) (order : Array Nat) : TermElabM Term := do
  let ys ← ctor.fields.mapM fun _ => fresh `y
  let sortedYs := order.map (ys[·]!)
  `(fun $sortedYs:ident* => $(← ctorApp ctor (ys.map (⟨·.raw⟩))))

def decodeAltBody (ctor : Ctor) (read : Fld → Term) : TermElabM Term := do
  let tag := strLit ctor.tag
  match ctor.shape with
    | .noArgs => do `(ExactJSON.Derive.noArgs $tag $(← ctorApp ctor #[]))
    | .single => do
      let p ← fresh `p
      `(ExactJSON.Derive.withPayload $tag (fun $p => $(← ctorLambda ctor #[0]) <$> $(read ctor.fields[0]!) $p))
    | .positional => do
      let order := Array.range ctor.fields.size
      let r ← readerTerm ctor.fields (← ctorLambda ctor order) read false (fun i => s!"[{i}]") order
      `(ExactJSON.Derive.withPayload $tag (ExactJSON.Derive.decodeItems $tag $(quote ctor.fields.size) $r))
    | .named => do
      let order := keyOrder ctor.fields
      let r ← readerTerm ctor.fields (← ctorLambda ctor order) read true (ctor.fields[·]!.key) order
      `(ExactJSON.Derive.withPayload $tag (ExactJSON.Derive.decodeFields $tag $(← schemaTerm ctor.fields) $r))

def decodeAlt (ctor : Ctor) (read : Fld → Term) : TermElabM Term := do
  `(($(strLit ctor.tag), $(← decodeAltBody ctor read)))

def typeLabel (declName : Name) : Term := strLit (privateToUserName declName.eraseMacroScopes).toString

def mkFromValueCmds (declName : Name) : TermElabM (Array Command) := do
  let indVal ← getConstInfoInduct declName
  checkType indVal
  let ctx ← mkContext ``FromValue "fromValue" declName
  let auxFrom := auxName declName "fromValue"
  let auxStep := auxName declName "step"
  let ps ← params indVal
  let binders ← instBinders ps [``FromValue]
  let v ← fresh `v
  let resultType ← `(Except String $(ps.indType))
  let inst ← `(instance $(mkIdent ctx.instName):ident $binders:bracketedBinder* : ExactJSON.FromValue $(ps.indType) := ⟨$auxFrom⟩)
  if isStructure (← getEnv) declName then
    let fields ← structFields indVal
    let r ← readerTerm fields (← structLambda fields ps.indType) (fun _ => ⟨mkIdent ``ExactJSON.fromValue?⟩) true
      (fields[·]!.key) (keyOrder fields)
    return #[← `(def $auxFrom:ident $binders:bracketedBinder* ($v : ExactJSON.Value) : $resultType :=
      ExactJSON.Derive.decodeFields $(typeLabel declName) $(← schemaTerm fields) $r $v), inst]
  let ctors := sortByKey (← ctorsOf indVal) (·.tag)
  if !indVal.isRec then
    let alts ← ctors.mapM fun c => decodeAlt c fun _ => ⟨mkIdent ``ExactJSON.fromValue?⟩
    return #[← `(def $auxFrom:ident $binders:bracketedBinder* ($v : ExactJSON.Value) : $resultType :=
      ExactJSON.Derive.decodeTagged [$alts,*] $v), inst]
  let decode ← fresh `decode
  let alts ← ctors.mapM fun c => decodeAlt c fun f => if f.recursive then ⟨decode⟩ else ⟨mkIdent ``ExactJSON.fromValue?⟩
  return #[
    ← `(def $auxStep:ident $binders:bracketedBinder* ($decode : ExactJSON.Value → $resultType) ($v : ExactJSON.Value) :
      $resultType := ExactJSON.Derive.decodeTagged [$alts,*] $v),
    ← `(def $auxFrom:ident $binders:bracketedBinder* ($v : ExactJSON.Value) : $resultType :=
      ExactJSON.Derive.fix $auxStep $v), inst]

def fitsTerm (fields : Array Fld) (order : Array Nat) : TermElabM Term := do
  let mut t ← `(ExactJSON.Derive.Fits.nil)
  for i in order.reverse do
    t ← if fields[i]!.optional then `(ExactJSON.Derive.Fits.opt $t) else `(ExactJSON.Derive.Fits.req $t)
  return t

def readsTerm (fields : Array Fld) (lam : Term) (order : Array Nat) (useOpt : Bool) (fact : Nat → TermElabM Term)
    (value : Nat → Term) : TermElabM Term := do
  let mut t ← `(ExactJSON.Derive.Reads.pure (b := $lam))
  let mut done : Array Term := #[]
  for i in order do
    let h ← if useOpt && fields[i]!.optional then
        `(ExactJSON.Derive.opt_map ExactJSON.LawfulValue.fromValue_toValue $(← fact i))
      else `(ExactJSON.Derive.req_some $(← fact i))
    let g ← if done.isEmpty then pure lam else `($lam $done*)
    t ← `(ExactJSON.Derive.Reads.ap (g := $g) (a := $(value i)) $t $h)
    done := done.push (value i)
  return t

def allValidTerm (fields : Array Fld) (order : Array Nat) (access : Nat → Term) (valid : Nat → TermElabM Term) :
    TermElabM Term := do
  let mut t ← `(ExactJSON.Derive.AllValid.nil)
  for i in order.reverse do
    t ← if fields[i]!.optional then
        `(ExactJSON.Derive.AllValid.map ExactJSON.LawfulValue.toValue_valid $(access i) $t)
      else `(ExactJSON.Derive.AllValid.some $(← valid i) $t)
  return t

def mkLawfulValueCmds (declName : Name) : TermElabM (Array Command) := do
  let indVal ← getConstInfoInduct declName
  checkType indVal
  let auxTo := auxName declName "toValue"
  let auxStep := auxName declName "step"
  let ps ← params indVal
  let binders ← instBinders ps [``ToValue, ``FromValue, ``LawfulValue]
  let instName := mkIdent (← mkInstName ``LawfulValue declName)
  let x ← fresh `x
  if isStructure (← getEnv) declName then
    let fields ← structFields indVal
    let order := keyOrder fields
    let access ← (Array.range fields.size).mapM fun i => `($x.$(mkIdent fields[i]!.name):ident)
    let lam ← structLambda fields ps.indType
    let b ← if fields.isEmpty then pure lam else `($lam $(order.map (access[·]!))*)
    let reads ← readsTerm fields lam order true (fun i =>
      if fields[i]!.optional then pure access[i]! else `(ExactJSON.LawfulValue.fromValue_toValue $(access[i]!)))
      (access[·]!)
    let valid ← allValidTerm fields order (access[·]!) fun i => `(ExactJSON.LawfulValue.toValue_valid $(access[i]!))
    let r ← readerTerm fields lam (fun _ => ⟨mkIdent ``ExactJSON.fromValue?⟩) true (fields[·]!.key) order
    let es ← order.mapM fun i => entryTerm auxTo fields[i]! access[i]!
    return #[← `(instance $instName:ident $binders:bracketedBinder* : ExactJSON.LawfulValue $(ps.indType) where
      fromValue_toValue := fun $x => ExactJSON.Derive.decodeFields_record (name := $(typeLabel declName))
        (schema := $(← schemaTerm fields)) (es := [$es,*]) (r := $r) (b := $b) $(← keysSorted (sortedKeys fields))
        $(← fitsTerm fields order) $reads
      toValue_valid := fun $x => ExactJSON.Derive.valid_record (schema := $(← schemaTerm fields))
        $(← keysSorted (sortedKeys fields)) $valid)]
  let ctors ← ctorsOf indVal
  let sorted := sortByKey ctors (·.tag)
  let tags := sorted.map (strLit ·.tag)
  let hn ← fresh `hn
  let ih ← fresh `ih
  let fieldFact (vars : Array Ident) (ctor : Ctor) (depth : Nat → TermElabM Term) (i : Nat) : TermElabM Term :=
    if ctor.fields[i]!.recursive then do `($ih $(vars[i]!) $(← depth i))
    else if ctor.fields[i]!.optional && ctor.shape matches .named then pure vars[i]!
    else `(ExactJSON.LawfulValue.fromValue_toValue $(vars[i]!))
  let fieldValid (vars : Array Ident) (ctor : Ctor) (depth : Nat → TermElabM Term) (i : Nat) : TermElabM Term :=
    if ctor.fields[i]!.recursive then do `($ih $(vars[i]!) $(← depth i))
    else `(ExactJSON.LawfulValue.toValue_valid $(vars[i]!))
  let depthOf (ctor : Ctor) (i : Nat) : TermElabM Term := do
    match ctor.shape with
    | .noArgs | .single => `(ExactJSON.Derive.depth_ofTag_some)
    | .positional => `(ExactJSON.Derive.depth_ofTag_array $(← memTerm i))
    | .named =>
      let order := keyOrder ctor.fields
      `(ExactJSON.Derive.depth_ofTag_record $(← fitsTerm ctor.fields order) $(← memTerm (order.idxOf i)))
  let decode ← fresh `decode
  let readField (f : Fld) : Term := if f.recursive then ⟨decode⟩ else ⟨mkIdent ``ExactJSON.fromValue?⟩
  let encField (f : Fld) (x : Ident) : TermElabM Term :=
    if f.recursive then `($auxTo $x) else `(ExactJSON.toValue $x)
  let roundTrip (ctor : Ctor) (vars : Array Ident) : TermElabM Term := do
    let fact := fieldFact vars ctor (depthOf ctor)
    let j := (sorted.findIdx? (·.name == ctor.name)).getD 0
    let alts ← sorted.mapM fun c => decodeAlt c readField
    let head ← `(tactic| refine (ExactJSON.Derive.decodeTagged_ofTag (alts := [$alts,*]) (n := $(strLit ctor.tag))
      (p := $(← ctorPayload auxTo ctor vars)) (alt := $(← decodeAltBody ctor readField))
      (by exact ExactJSON.Derive.nodup_of_increase $hn) (by exact $(← memTerm j))).trans ?_)
    let payload ← match ctor.shape with
      | .noArgs => `(ExactJSON.Derive.noArgs_none)
      | .single => do `(ExactJSON.Derive.withPayload_map (f := $(← ctorLambda ctor #[0])) $(← fact 0))
      | .positional => do
        let order := Array.range ctor.fields.size
        let lam ← ctorLambda ctor order
        let b ← `($lam $(order.map (fun i => (⟨vars[i]!.raw⟩ : Term)))*)
        let r ← readerTerm ctor.fields lam readField false (fun i => s!"[{i}]") order
        let xs ← order.mapM fun i => encField ctor.fields[i]! vars[i]!
        `(ExactJSON.Derive.withPayload_items (xs := [$xs,*]) (r := $r) (b := $b) rfl
          $(← readsTerm ctor.fields lam order false fact (fun i => ⟨vars[i]!.raw⟩)))
      | .named => do
        let order := keyOrder ctor.fields
        let lam ← ctorLambda ctor order
        let b ← `($lam $(order.map (fun i => (⟨vars[i]!.raw⟩ : Term)))*)
        let r ← readerTerm ctor.fields lam readField true (ctor.fields[·]!.key) order
        let es ← order.mapM fun i => entryTerm auxTo ctor.fields[i]! ⟨vars[i]!.raw⟩
        `(ExactJSON.Derive.withPayload_fields (name := $(strLit ctor.tag)) (schema := $(← schemaTerm ctor.fields))
          (es := [$es,*]) (r := $r) (b := $b) $(← keysSorted (sortedKeys ctor.fields))
          $(← fitsTerm ctor.fields order) $(← readsTerm ctor.fields lam order true fact (fun i => ⟨vars[i]!.raw⟩)))
    `(by $head:tactic; exact $payload)
  let validity (ctor : Ctor) (vars : Array Ident) : TermElabM Term := do
    let v := fieldValid vars ctor (depthOf ctor)
    match ctor.shape with
    | .noArgs => `(ExactJSON.Derive.valid_ofTag_none)
    | .single => do `(ExactJSON.Derive.valid_ofTag_some $(← v 0))
    | .positional => do
      let mut t ← `(ExactJSON.Derive.itemsValid_nil)
      for i in (Array.range ctor.fields.size).reverse do
        t ← `(ExactJSON.Derive.itemsValid_cons $(← v i) $t)
      `(ExactJSON.Derive.valid_ofTag_some (ExactJSON.Derive.valid_array $t))
    | .named => do
      let order := keyOrder ctor.fields
      `(ExactJSON.Derive.valid_ofTag_some (ExactJSON.Derive.valid_record (schema := $(← schemaTerm ctor.fields))
        $(← keysSorted (sortedKeys ctor.fields))
        $(← allValidTerm ctor.fields order (fun i => vars[i]!) v)))
  let a ← fresh `a
  let mut rtAlts := #[]
  let mut vAlts := #[]
  for ctor in ctors do
    let vars ← ctor.fields.mapM fun _ => fresh `a
    let pat ← ctorPattern indVal ctor vars
    rtAlts := rtAlts.push (← `(matchAltExpr| | $pat:term => $(← roundTrip ctor vars)))
    vAlts := vAlts.push (← `(matchAltExpr| | $pat:term => $(← validity ctor vars)))
  let names ← `([$tags,*])
  if !indVal.isRec then
    return #[← `(instance $instName:ident $binders:bracketedBinder* : ExactJSON.LawfulValue $(ps.indType) where
      fromValue_toValue := fun $x =>
        have $hn : ExactJSON.keysIncrease $names = true := $(← keysSortedProof (sorted.map (·.tag)))
        match $x:ident with $rtAlts:matchAlt*
      toValue_valid := fun $x => match $x:ident with $vAlts:matchAlt*)]
  return #[← `(instance $instName:ident $binders:bracketedBinder* : ExactJSON.LawfulValue $(ps.indType) where
    fromValue_toValue := fun $x =>
      have $hn : ExactJSON.keysIncrease $names = true := $(← keysSortedProof (sorted.map (·.tag)))
      ExactJSON.Derive.fix_ok $auxStep $auxTo (fun $decode $a $ih => match $a:ident with $rtAlts:matchAlt*) $x
    toValue_valid := ExactJSON.Derive.valid_of_depth $auxTo (fun $a $ih => match $a:ident with $vAlts:matchAlt*))]

def runHandler (mk : Name → TermElabM (Array Command)) (declNames : Array Name) : CommandElabM Bool := do
  if declNames.isEmpty || !(← declNames.allM isInductive) then return false
  for declName in declNames do
    let cmds ← liftTermElabM (mk declName)
    cmds.forM elabCommand
  return true

initialize
  registerDerivingHandler ``ToValue (runHandler mkToValueCmds)
  registerDerivingHandler ``FromValue (runHandler mkFromValueCmds)
  registerDerivingHandler ``LawfulValue (runHandler mkLawfulValueCmds)

end ExactJSON.Derive

end
