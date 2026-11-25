module

public import ExactJSON.ReadLaws
public import ExactJSON.LinesLaws
public import ExactJSON.Printable

public section

namespace ExactJSON

universe u

theorem encode_eq {α : Type u} [ToValue α] (a : α) : encode a = (toValue a).render := rfl

theorem typed_ok {α : Type u} [ToValue α] [FromValue α] (v : Value) (a : α) :
    typed v = .ok a ↔ v = toValue a ∧ fromValue? (toValue a) = .ok a := by
  unfold typed
  constructor
  · intro h
    split at h
    · cases h
    · rename_i a' ha'
      split at h
      · rename_i hbeq
        cases h
        have hv := beq_iff_eq.mp hbeq
        exact ⟨hv.symm, hv ▸ ha'⟩
      · cases h
  · rintro ⟨rfl, ha⟩
    rw [ha]
    simp only
    rw [ite_eq_left (show (toValue a == toValue a) = true from beq_self_eq_true _)]

theorem decode_eq {α : Type u} [ToValue α] [FromValue α] (maxDepth : Nat) (b : ByteArray) (a : α) :
    decode maxDepth b = .ok a ↔
      Value.read .canonical maxDepth b = .ok (toValue a) ∧ fromValue? (toValue a) = .ok a := by
  unfold decode
  constructor
  · intro h
    split at h
    · cases h
    · rename_i v hv
      obtain ⟨rfl, ha⟩ := (typed_ok v a).mp h
      exact ⟨hv, ha⟩
  · rintro ⟨hv, ha⟩
    rw [hv]
    exact (typed_ok _ a).mpr ⟨rfl, ha⟩

theorem mapM_typed_sound {α : Type u} [ToValue α] [FromValue α] :
    ∀ (vs : List Value) (as : List α), vs.mapM typed = .ok as →
      vs = as.map toValue ∧ ∀ a ∈ as, fromValue? (toValue a) = .ok a
  | [], as, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | v :: vs, as, h => by
    simp only [List.mapM_cons] at h
    cases ht : (typed v : Except String α) with
    | error e =>
      rw [ht] at h
      cases h
    | ok a =>
      rw [ht] at h
      cases hm : vs.mapM (typed : Value → Except String α) with
      | error e =>
        simp only [bind, Except.bind, hm] at h
        cases h
      | ok as' =>
        simp only [bind, Except.bind, hm, pure, Except.pure, Except.ok.injEq] at h
        subst h
        obtain ⟨rfl, ha⟩ := (typed_ok v a).mp ht
        obtain ⟨rfl, hall⟩ := mapM_typed_sound vs as' hm
        refine ⟨rfl, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hall x hx

theorem mapM_typed_complete {α : Type u} [ToValue α] [FromValue α] :
    ∀ (as : List α), (∀ a ∈ as, fromValue? (toValue a) = .ok a) → (as.map toValue).mapM typed = .ok as
  | [], _ => rfl
  | a :: as, h => by
    simp only [List.map_cons, List.mapM_cons]
    rw [(typed_ok (toValue a) a).mpr ⟨rfl, h a List.mem_cons_self⟩,
      mapM_typed_complete as (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    rfl

theorem decodeLines_eq {α : Type u} [ToValue α] [FromValue α] (maxDepth : Nat) (b : ByteArray) (as : Array α) :
    decodeLines maxDepth b = .ok as ↔
      Value.readLines .canonical maxDepth b = .ok (as.map toValue) ∧ ∀ a ∈ as, fromValue? (toValue a) = .ok a := by
  unfold decodeLines
  constructor
  · intro h
    split at h
    · cases h
    · rename_i vs hvs
      cases hm : vs.toList.mapM (typed : Value → Except String α) with
      | error e =>
        rw [hm] at h
        cases h
      | ok as' =>
        rw [hm] at h
        simp only [Functor.map, Except.map, Except.ok.injEq] at h
        subst h
        obtain ⟨hv, hall⟩ := mapM_typed_sound _ _ hm
        refine ⟨?_, fun a ha => hall a (by simpa using ha)⟩
        rw [hvs]
        congr 1
        apply Array.toList_inj.mp
        simp [hv]
  · rintro ⟨hvs, hall⟩
    rw [hvs]
    simp only [Array.toList_map]
    rw [mapM_typed_complete as.toList (fun a ha => hall a (by simpa using ha))]
    rfl

theorem decode_encode {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] (maxDepth : Nat) (a : α)
    (h : (toValue a).depth ≤ maxDepth) : decode maxDepth (encode a).toUTF8 = .ok a := by
  rw [decode_eq, read_spelling]
  exact ⟨⟨⟨LawfulValue.toValue_valid a, by rw [encode_eq, Value.render_eq_write]⟩, h⟩,
    LawfulValue.fromValue_toValue a⟩

theorem ten_mem_utf8EncodeChar {c : Char} (h : (10 : UInt8) ∈ String.utf8EncodeChar c) : c = '\n' := by
  have key : ∀ n : Nat, (10 : UInt8) = UInt8.ofNat n → n % 256 = 10 := by
    intro n hn
    have := congrArg UInt8.toNat hn
    simp [UInt8.toNat_ofNat] at this
    omega
  unfold String.utf8EncodeChar at h
  simp only at h
  by_cases h1 : c.val.toNat ≤ 127
  · rw [ite_eq_left h1] at h
    have h10 := key _ (List.mem_singleton.mp h)
    apply Char.ext
    apply UInt32.toNat_inj.mp
    show c.val.toNat = 10
    omega
  · rw [ite_eq_right h1] at h
    by_cases h2 : c.val.toNat ≤ 2047
    · rw [ite_eq_left h2] at h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> (have := key _ h; omega)
    · rw [ite_eq_right h2] at h
      by_cases h3 : c.val.toNat ≤ 65535
      · rw [ite_eq_left h3] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h <;> (have := key _ h; omega)
      · rw [ite_eq_right h3] at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with h | h | h | h <;> (have := key _ h; omega)

theorem bytes_no_lf {s : String} (h : '\n' ∉ s.toList) : (10 : UInt8) ∉ s.toByteArray.data.toList := by
  intro h10
  rw [← String.ofList_toList (s := s), String.toByteArray_ofList] at h10
  simp only [List.utf8Encode, List.data_toByteArray, List.toList_toArray] at h10
  obtain ⟨c, hc, h10⟩ := List.mem_flatMap.mp h10
  exact h (ten_mem_utf8EncodeChar h10 ▸ hc)

theorem utf8_lines (l : List String) :
    (String.join (l.map (· ++ "\n"))).toByteArray.data.toList =
      (l.map fun s => s.toByteArray.data.toList ++ [10]).flatten := by
  induction l with
  | nil => simp
  | cons s l ih =>
    simp only [List.map_cons, String.join_cons, String.toByteArray_append, ByteArray.toList_data_append, ih,
      List.flatten_cons, List.append_assoc]
    rfl

theorem mapM_read_map {α : Type} (f : α → ByteArray) (g : α → Value) (read : ByteArray → Except String Value) :
    ∀ (l : List α), (∀ x ∈ l, read (f x) = .ok (g x)) → (l.map f).mapM read = .ok (l.map g)
  | [], _ => rfl
  | x :: l, h => by
    simp only [List.map_cons, List.mapM_cons]
    rw [h x List.mem_cons_self, mapM_read_map f g read l (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    rfl

theorem readLines_renderLines (maxDepth : Nat) (vs : Array Value) (hv : ∀ v ∈ vs, v.Valid)
    (hd : ∀ v ∈ vs, v.depth ≤ maxDepth) : Value.readLines .canonical maxDepth (Value.renderLines vs).toUTF8 = .ok vs := by
  rw [readLines_framing]
  refine ⟨vs.toList.map fun v => v.render.toUTF8, ?_, ?_, ?_⟩
  · rw [renderLines_eq, show (String.join (vs.toList.map fun v => v.render ++ "\n")) =
      String.join ((vs.toList.map Value.render).map (· ++ "\n")) by simp [Function.comp_def]]
    show (String.join _).toByteArray.data.toList = _
    rw [utf8_lines]
    simp [Function.comp_def]
  · intro l hl
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hl
    exact bytes_no_lf (fun hc => absurd (printable_render v '\n' hc).1 (by decide))
  · have := mapM_read_map (fun v => v.render.toUTF8) id (Value.read .canonical maxDepth) vs.toList (by
      intro v hvm
      rw [read_spelling]
      exact ⟨⟨hv v (by simpa using hvm), by rw [Value.render_eq_write]; rfl⟩, hd v (by simpa using hvm)⟩)
    simpa using this

theorem decodeLines_encode {α : Type u} [ToValue α] [FromValue α] [LawfulValue α] (maxDepth : Nat) (as : Array α)
    (h : ∀ a ∈ as, (toValue a).depth ≤ maxDepth) : decodeLines maxDepth (encodeLines as).toUTF8 = .ok as := by
  rw [decodeLines_eq, encodeLines_eq]
  refine ⟨readLines_renderLines maxDepth _ ?_ ?_, fun a _ => LawfulValue.fromValue_toValue a⟩
  · intro v hv
    obtain ⟨a, -, rfl⟩ := Array.mem_map.mp hv
    exact LawfulValue.toValue_valid a
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp hv
    exact h a ha

theorem encode_eq_rejects_empty :
    ¬ ∀ {α : Type u} [ToValue α] (a : α), (fun {β : Type u} [ToValue β] (_ : β) => "") a = (toValue a).render := by
  intro h
  have := @h PUnit ⟨fun _ => .null⟩ ⟨⟩
  rw [Value.render_eq_write] at this
  exact absurd this (by decide)

theorem decode_eq_rejects_failure :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (maxDepth : Nat) (b : ByteArray) (a : α),
      (fun {β : Type u} [ToValue β] [FromValue β] (_ : Nat) (_ : ByteArray) => (Except.error "" : Except String β))
          maxDepth b = .ok a ↔
        Value.read .canonical maxDepth b = .ok (toValue a) ∧ fromValue? (toValue a) = .ok a := by
  intro h
  have := (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ 0 "null".toUTF8 ⟨⟩).mpr
    ⟨(read_spelling .canonical 0 _ _).mpr ⟨⟨rfl, rfl⟩, Nat.zero_le _⟩, rfl⟩
  cases this

theorem decodeLines_eq_rejects_failure :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (maxDepth : Nat) (b : ByteArray) (as : Array α),
      (fun {β : Type u} [ToValue β] [FromValue β] (_ : Nat) (_ : ByteArray) =>
          (Except.error "" : Except String (Array β))) maxDepth b = .ok as ↔
        Value.readLines .canonical maxDepth b = .ok (as.map toValue) ∧ ∀ a ∈ as, fromValue? (toValue a) = .ok a := by
  intro h
  have := (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ 0 ByteArray.empty #[]).mpr
    ⟨(readLines_framing .canonical 0 _ _).mpr ⟨[], rfl, by simp, by simp [pure, Except.pure]⟩, fun _ h => absurd h (by simp)⟩
  cases this

end ExactJSON
