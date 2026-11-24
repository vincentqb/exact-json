module

public import ExactJSON.ShapesDerived

public section

namespace ExactJSON

private theorem pure_ok {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

private theorem map_ok {ε α β : Type} (f : α → β) (a : α) : (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

private theorem withContext_ok {α : Type} (c : String) (a : α) : withContext c (.ok a) = .ok a := rfl

private theorem tag?_string (s : String) : Derive.tag? (.string s) = .ok (s, none) := rfl

private theorem tag?_ctor (k : String) (p : Value) : Derive.tag? (.table #[(k, p)]) = .ok (k, some p) := rfl

private theorem payload_some (name : String) (p : Value) : Derive.payload name (some p) = .ok p := rfl

private theorem noPayload_none (name : String) : Derive.noPayload name none = .ok () := rfl

private theorem expectTable_table (name : String) (ms : Array (String × Value)) :
    Derive.expectTable name (.table ms) = .ok () := rfl

private theorem items_two (a b : Value) : Derive.items 2 (.array #[a, b]) = .ok #[a, b] := rfl

private theorem fuel_ok {α : Type} (step : (Value → Except String α) → Value → Except String α)
    (enc : α → Value)
    (hstep : ∀ (decode : Value → Except String α) (a : α),
      (∀ b, Derive.depth (enc b) < Derive.depth (enc a) → decode (enc b) = .ok b) → step decode (enc a) = .ok a) :
    ∀ n a, Derive.depth (enc a) < n → Derive.fuel step n (enc a) = .ok a := by
  intro n
  induction n with
  | zero => intro a h; exact absurd h (Nat.not_lt_zero _)
  | succ m ih => exact fun a h => hstep _ a fun b hb => ih b (by omega)

private theorem fix_ok {α : Type} (step : (Value → Except String α) → Value → Except String α)
    (enc : α → Value)
    (hstep : ∀ (decode : Value → Except String α) (a : α),
      (∀ b, Derive.depth (enc b) < Derive.depth (enc a) → decode (enc b) = .ok b) → step decode (enc a) = .ok a)
    (a : α) : Derive.fix step (enc a) = .ok a :=
  fuel_ok step enc hstep _ a (Nat.lt_succ_self _)

private theorem fromValue_nat (n : Nat) : fromValue? (toValue n) = .ok n := by
  simp [toValue, fromValue?, pure_ok]

private theorem fromValue_int (n : Int) : fromValue? (toValue n) = .ok n := rfl

private theorem fromValue_string (s : String) : fromValue? (toValue s) = .ok s := rfl

private theorem fromValue_none : (fromValue? (toValue (none : Option String)) : Except String (Option String)) = .ok none :=
  rfl

private theorem fromValue_some (s : String) :
    (fromValue? (toValue (some s)) : Except String (Option String)) = .ok (some s) := rfl

private theorem toValue_dot : toValue Example.Shape.dot = .string "dot" := rfl

private theorem toValue_circle (r : Nat) :
    toValue (Example.Shape.circle r) = .table #[("circle", .table #[("radius", toValue r)])] := rfl

private theorem toValue_rect (w h : Nat) :
    toValue (Example.Shape.rect w h) = .table #[("rect", .table #[("height", toValue h), ("width", toValue w)])] := rfl

private theorem toValue_tagged (n : Nat) : toValue (Example.Shape.tagged n) = .table #[("tagged", toValue n)] := rfl

private theorem toValue_pair (n : Nat) (t : String) :
    toValue (Example.Shape.pair n t) = .table #[("pair", .array #[toValue n, toValue t])] := rfl

private theorem toValue_scaled (f : Nat) (inner : Example.Shape) :
    toValue (Example.Shape.scaled f inner) =
      .table #[("scaled", .table #[("factor", toValue f), ("inner", toValue inner)])] := rfl

private theorem fromValue_shape (s : Example.Shape) : fromValue? (toValue s) = .ok s := by
  change Example.instFromValueShape.fromValue (toValue s) = _
  unfold Example.instFromValueShape.fromValue
  refine fix_ok _ toValue (fun decode s ih => ?_) s
  cases s with
  | scaled f inner =>
    have h := ih inner (by simp [toValue_scaled, Derive.depth, Derive.depthMembers]; omega)
    simp [toValue_scaled, pure_ok, ok_bind, withContext_ok, tag?_ctor, payload_some, expectTable_table,
      fromValue_nat, Derive.onlyKeys, FromField.getField?, Value.get?, Derive.fieldWith, h]
  | _ =>
    simp [toValue_dot, toValue_circle, toValue_rect, toValue_tagged, toValue_pair, pure_ok, ok_bind, withContext_ok,
      tag?_string, tag?_ctor, payload_some, noPayload_none, expectTable_table, items_two, fromValue_nat,
      fromValue_string, Derive.onlyKeys, FromField.getField?, Value.get?]

theorem codec_point (p : Example.Point) :
    toValue p = .table ((match p.label? with | none => #[] | some l => #[("label", toValue l)]) ++
      #[("x", toValue p.x), ("y", toValue p.y)]) ∧
      fromValue? (toValue p) = .ok p := by
  obtain ⟨x, y, label?⟩ := p
  have h : toValue (Example.Point.mk x y label?) =
      .table ((match label? with | none => #[] | some l => #[("label", toValue l)]) ++
        #[("x", toValue x), ("y", toValue y)]) := by
    cases label? <;> rfl
  refine ⟨h, ?_⟩
  change Example.instFromValuePoint.fromValue _ = _
  rw [h]
  cases label? <;>
  simp [Example.instFromValuePoint.fromValue, pure_ok, ok_bind, map_ok, withContext_ok, expectTable_table,
    fromValue_int, fromValue_string, Derive.onlyKeys, FromField.getField?, Value.get?]

theorem codec_shape (s : Example.Shape) :
    toValue s = (match s with
      | .dot => .string "dot"
      | .circle r => .table #[("circle", .table #[("radius", toValue r)])]
      | .rect w h => .table #[("rect", .table #[("height", toValue h), ("width", toValue w)])]
      | .tagged n => .table #[("tagged", toValue n)]
      | .pair n t => .table #[("pair", .array #[toValue n, toValue t])]
      | .scaled f inner => .table #[("scaled", .table #[("factor", toValue f), ("inner", toValue inner)])]) ∧
      fromValue? (toValue s) = .ok s :=
  ⟨by cases s <;> rfl, fromValue_shape s⟩

theorem codec_envelope (e : Example.Envelope) :
    toValue e = .table (#[("id", toValue e.id)] ++
      (match e.note? with | none => #[] | some n => #[("note", toValue n)]) ++ #[("shape", toValue e.shape)]) ∧
      fromValue? (toValue e) = .ok e := by
  obtain ⟨id, note?, shape⟩ := e
  have h : toValue (Example.Envelope.mk id note? shape) = .table (#[("id", toValue id)] ++
      (match note? with | none => #[] | some n => #[("note", toValue n)]) ++ #[("shape", toValue shape)]) := by
    cases note? <;> rfl
  refine ⟨h, ?_⟩
  change Example.instFromValueEnvelope.fromValue _ = _
  rw [h]
  rcases note? with _ | _ | n <;>
  simp [Example.instFromValueEnvelope.fromValue, pure_ok, ok_bind, map_ok, withContext_ok, expectTable_table,
    fromValue_nat, fromValue_none, fromValue_some, fromValue_shape, Derive.onlyKeys, FromField.getField?, Value.get?]

theorem codec_point_rejects_null :
    ¬ ∀ (p : Example.Point),
      @toValue Example.Point ⟨fun _ => .null⟩ p = .table ((match p.label? with | none => #[] | some l => #[("label", toValue l)]) ++
        #[("x", toValue p.x), ("y", toValue p.y)]) ∧
        @fromValue? Example.Point ⟨fun _ => .error ""⟩ (@toValue Example.Point ⟨fun _ => .null⟩ p) = .ok p := by
  intro h
  cases (h ⟨0, 0, none⟩).1

theorem codec_shape_rejects_null :
    ¬ ∀ (s : Example.Shape),
      @toValue Example.Shape ⟨fun _ => .null⟩ s = (match s with
        | .dot => .string "dot"
        | .circle r => .table #[("circle", .table #[("radius", toValue r)])]
        | .rect w h => .table #[("rect", .table #[("height", toValue h), ("width", toValue w)])]
        | .tagged n => .table #[("tagged", toValue n)]
        | .pair n t => .table #[("pair", .array #[toValue n, toValue t])]
        | .scaled f inner =>
          .table #[("scaled", .table #[("factor", toValue f), ("inner", @toValue Example.Shape ⟨fun _ => .null⟩ inner)])]) ∧
        @fromValue? Example.Shape ⟨fun _ => .error ""⟩ (@toValue Example.Shape ⟨fun _ => .null⟩ s) = .ok s := by
  intro h
  cases (h .dot).1

theorem codec_envelope_rejects_null :
    ¬ ∀ (e : Example.Envelope),
      @toValue Example.Envelope ⟨fun _ => .null⟩ e = .table (#[("id", toValue e.id)] ++
        (match e.note? with | none => #[] | some n => #[("note", toValue n)]) ++ #[("shape", toValue e.shape)]) ∧
        @fromValue? Example.Envelope ⟨fun _ => .error ""⟩ (@toValue Example.Envelope ⟨fun _ => .null⟩ e) = .ok e := by
  intro h
  cases (h ⟨0, none, .dot⟩).1

end ExactJSON
