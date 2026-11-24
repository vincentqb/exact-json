module

public import ExactJSON.ShapesDerived

public section

namespace ExactJSON

theorem codec_point (p : Example.Point) :
    toValue p = .table ((match p.label? with | none => #[] | some l => #[("label", toValue l)]) ++
      #[("x", toValue p.x), ("y", toValue p.y)]) := by
  obtain ⟨x, y, label?⟩ := p
  cases label? <;> rfl

theorem codec_shape (s : Example.Shape) :
    toValue s = (match s with
      | .dot => .string "dot"
      | .circle r => .table #[("circle", .table #[("radius", toValue r)])]
      | .rect w h => .table #[("rect", .table #[("height", toValue h), ("width", toValue w)])]
      | .tagged n => .table #[("tagged", toValue n)]
      | .pair n t => .table #[("pair", .array #[toValue n, toValue t])]
      | .scaled f inner => .table #[("scaled", .table #[("factor", toValue f), ("inner", toValue inner)])]) := by
  cases s <;> rfl

theorem codec_envelope (e : Example.Envelope) :
    toValue e = .table (#[("id", toValue e.id)] ++
      (match e.note? with | none => #[] | some none => #[("note", .null)] | some (some n) => #[("note", toValue n)]) ++
      #[("shape", toValue e.shape)]) := by
  obtain ⟨id, note?, shape⟩ := e
  rcases note? with _ | _ | n <;> rfl

theorem lawful_examples : LawfulValue Example.Point ∧ LawfulValue Example.Shape ∧ LawfulValue Example.Envelope :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem codec_point_rejects_null :
    ¬ ∀ (p : Example.Point),
      @toValue Example.Point ⟨fun _ => .null⟩ p = .table ((match p.label? with | none => #[] | some l => #[("label", toValue l)]) ++
        #[("x", toValue p.x), ("y", toValue p.y)]) := by
  intro h
  cases h ⟨0, 0, none⟩

theorem codec_shape_rejects_null :
    ¬ ∀ (s : Example.Shape),
      @toValue Example.Shape ⟨fun _ => .null⟩ s = (match s with
        | .dot => .string "dot"
        | .circle r => .table #[("circle", .table #[("radius", toValue r)])]
        | .rect w h => .table #[("rect", .table #[("height", toValue h), ("width", toValue w)])]
        | .tagged n => .table #[("tagged", toValue n)]
        | .pair n t => .table #[("pair", .array #[toValue n, toValue t])]
        | .scaled f inner =>
          .table #[("scaled", .table #[("factor", toValue f), ("inner", @toValue Example.Shape ⟨fun _ => .null⟩ inner)])]) := by
  intro h
  cases h .dot

theorem codec_envelope_rejects_null :
    ¬ ∀ (e : Example.Envelope),
      @toValue Example.Envelope ⟨fun _ => .null⟩ e = .table (#[("id", toValue e.id)] ++
        (match e.note? with | none => #[] | some none => #[("note", .null)] | some (some n) => #[("note", toValue n)]) ++
        #[("shape", toValue e.shape)]) := by
  intro h
  cases h ⟨0, none, .dot⟩

theorem lawful_examples_rejects_failure :
    ¬ (@LawfulValue Example.Point Example.instToValuePoint ⟨fun _ => .error ""⟩ ∧ LawfulValue Example.Shape ∧
      LawfulValue Example.Envelope) := by
  intro ⟨h, _, _⟩
  cases h.fromValue_toValue ⟨0, 0, none⟩

end ExactJSON
