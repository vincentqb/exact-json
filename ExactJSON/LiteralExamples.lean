module

public import ExactJSON.Literal

public section

namespace ExactJSON

@[expose] def literalExample : Value := exactjson% {"d": -3, "c": [null, true, "x"], "b": 2.5, "a": 1}

@[expose] def literalSplice (n : Nat) (s : String) : Value := exactjson% {name: $(s), count: $(n)}

theorem literalExample_eq :
    literalExample = .table #[("a", .integer 1), ("b", .float 2.5),
      ("c", .array #[.null, .boolean true, .string "x"]), ("d", .integer (-3))] := rfl

theorem literalSplice_eq (n : Nat) (s : String) :
    literalSplice n s = .table #[("count", toValue n), ("name", toValue s)] := rfl

theorem literalExample_eq_rejects_null :
    ¬ (Value.null : Value) = .table #[("a", .integer 1), ("b", .float 2.5),
      ("c", .array #[.null, .boolean true, .string "x"]), ("d", .integer (-3))] := nofun

theorem literalSplice_eq_rejects_null :
    ¬ ∀ (n : Nat) (s : String), (fun (_ : Nat) (_ : String) => Value.null) n s =
      .table #[("count", toValue n), ("name", toValue s)] := fun h => nomatch h 0 ""

end ExactJSON
