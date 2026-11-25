module

public import ExactJSON.Codec
public import ExactJSON.Text

public section

namespace ExactJSON

universe u

private theorem foldl_renderLines (l : List Value) (out : String) :
    l.foldl (fun out v => (Value.renderTo out v).push '\n') out =
      out ++ String.join (l.map fun v => v.render ++ "\n") := by
  induction l generalizing out with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, ih]
    apply String.ext
    simp [String.toList_append, String.toList_push, Value.renderTo_toList out v, Value.render]

theorem renderLines_eq (vs : Array Value) :
    Value.renderLines vs = String.join (vs.toList.map fun v => v.render ++ "\n") := by
  rw [Value.renderLines, ← Array.foldl_toList, foldl_renderLines, String.empty_append]

theorem encodeLines_eq {α : Type u} [ToValue α] (as : Array α) :
    encodeLines as = Value.renderLines (as.map toValue) := by
  rw [encodeLines, Value.renderLines, Array.foldl_map]

theorem renderLines_eq_rejects_empty :
    ¬ ∀ (vs : Array Value), (fun (_ : Array Value) => "") vs = String.join (vs.toList.map fun v => v.render ++ "\n") := by
  intro h
  have := congrArg String.toList (h #[.null])
  simp at this

theorem encodeLines_eq_rejects_constant :
    ¬ ∀ {α : Type u} [ToValue α] (as : Array α),
      (fun {β : Type u} [ToValue β] (_ : Array β) => "x") as = (fun (_ : Array Value) => "") (as.map toValue) := by
  intro h
  exact absurd (@h PUnit ⟨fun _ => .null⟩ #[]) (by decide)

end ExactJSON
