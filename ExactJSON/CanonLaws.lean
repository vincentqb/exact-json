module

public import ExactJSON.Main

public section

namespace ExactJSON

private theorem toOption_map {α β : Type} (f : α → β) (x : Except String α) :
    (x.map f).toOption = x.toOption.map f := by
  cases x <;> rfl

private theorem toOption_ok {α : Type} (a : α) : (Except.ok a : Except String α).toOption = some a := rfl

private theorem toOption_error {α : Type} (e : String) : (Except.error e : Except String α).toOption = none := rfl

private theorem readEach_toOption :
    ∀ (lines : List String) (number : Nat) (out : Array Value),
      (canon.readEach number out lines).toOption =
        (lines.mapM fun l => (Value.readJson l).toOption).map (out ++ ·.toArray)
  | [], number, out => by simp [canon.readEach, toOption_ok]
  | l :: lines, number, out => by
    simp only [canon.readEach]
    cases hr : Value.readJson l with
    | error e => simp [toOption_error, List.mapM_cons, hr]
    | ok v =>
      simp only
      rw [readEach_toOption lines (number + 1) (out.push v)]
      cases hm : lines.mapM fun l => (Value.readJson l).toOption with
      | none => simp [List.mapM_cons, hr, hm, toOption_ok]
      | some vs => simp [List.mapM_cons, hr, hm, toOption_ok]

private theorem mapM_some_null : ∀ (ls : List String),
    (ls.mapM fun (_ : String) => (some Value.null : Option Value)) = some (ls.map fun _ => Value.null)
  | [] => rfl
  | l :: ls => by simp [List.mapM_cons, mapM_some_null ls]

theorem canon_text (s : String) : canon false s = (Value.readJson s).map fun v => v.render ++ "\n" := by
  have hline : (fun v : Value => v.render.push '\n') = fun v => v.render ++ "\n" := by
    funext v
    apply String.ext
    simp [String.toList_push, String.toList_append]
  simp only [canon, Bool.false_eq_true, ↓reduceIte, hline]

theorem canon_lines (s : String) :
    (canon true s).toOption =
      ((jsonLines s).mapM fun l => (Value.readJson l).toOption).map fun vs => Value.renderLines vs.toArray := by
  simp only [canon, ↓reduceIte, toOption_map, readEach_toOption, Option.map_map]
  congr 1
  funext vs
  simp

theorem canon_text_rejects_empty :
    ¬ ∀ (s : String), (fun (_ : Bool) (_ : String) => (Except.ok "" : Except String String)) false s =
      ((fun (_ : String) => (Except.ok Value.null : Except String Value)) s).map fun v => (fun (_ : Value) => "null") v ++ "\n" := by
  intro h
  exact absurd (Except.ok.inj (h "")) (by decide)

theorem canon_lines_rejects_error :
    ¬ ∀ (s : String),
      ((fun (_ : Bool) (_ : String) => (Except.error "" : Except String String)) true s).toOption =
        ((jsonLines s).mapM fun l => ((fun (_ : String) => (Except.ok Value.null : Except String Value)) l).toOption).map
          fun vs => (fun (_ : Array Value) => "") vs.toArray := by
  intro h
  have := h ""
  simp [Except.toOption, mapM_some_null] at this

end ExactJSON
