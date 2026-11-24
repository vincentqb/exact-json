module

public import ExactJSON.Fixed
public import ExactJSON.OfScientific
public import ExactJSON.Printable
import all Init.Data.String.Legacy

public section

namespace ExactJSON

universe u

private def byteLen : List Char → Nat
  | [] => 0
  | c :: l => c.utf8Size + byteLen l

private theorem byteLen_append (a b : List Char) : byteLen (a ++ b) = byteLen a + byteLen b := by
  induction a with
  | nil => simp [byteLen]
  | cons c a ih => simp [byteLen, ih, Nat.add_assoc]

private theorem byteLen_pos {l : List Char} (h : l ≠ []) : 0 < byteLen l := by
  cases l with
  | nil => exact absurd rfl h
  | cons c l => simp only [byteLen]; have := c.utf8Size_pos; omega

private theorem utf8ByteSize_ofList (l : List Char) : (String.ofList l).utf8ByteSize = byteLen l := by
  induction l with
  | nil => simp [byteLen]
  | cons c l ih => simp [byteLen, ih, String.utf8ByteSize_singleton]

private theorem utf8ByteSize_eq (s : String) : s.utf8ByteSize = byteLen s.toList := by
  rw [← utf8ByteSize_ofList, String.ofList_toList]

private theorem utf8GetAux_at (c : Char) (post : List Char) :
    ∀ (pre : List Char) (n : Nat), String.Pos.Raw.utf8GetAux (pre ++ c :: post) ⟨n⟩ ⟨n + byteLen pre⟩ = c
  | [], n => by simp [String.Pos.Raw.utf8GetAux, byteLen]
  | d :: pre, n => by
    have hd := d.utf8Size_pos
    have h2 : n + byteLen (d :: pre) = n + d.utf8Size + byteLen pre := by simp [byteLen, Nat.add_assoc]
    have hne : (⟨n⟩ : String.Pos.Raw) ≠ ⟨n + d.utf8Size + byteLen pre⟩ := by simp; omega
    simp only [List.cons_append, String.Pos.Raw.utf8GetAux, h2, hne, ↓reduceIte]
    exact utf8GetAux_at c post pre (n + d.utf8Size)

private theorem extract_go₂ (post : List Char) :
    ∀ (mid : List Char) (n : Nat), String.Pos.Raw.extract.go₂ (mid ++ post) ⟨n⟩ ⟨n + byteLen mid⟩ = mid
  | [], n => by
    cases post <;> simp [String.Pos.Raw.extract.go₂, byteLen]
  | d :: mid, n => by
    have hd := d.utf8Size_pos
    have h2 : n + byteLen (d :: mid) = n + d.utf8Size + byteLen mid := by simp [byteLen, Nat.add_assoc]
    have hne : (⟨n⟩ : String.Pos.Raw) ≠ ⟨n + d.utf8Size + byteLen mid⟩ := by simp; omega
    simp only [List.cons_append, String.Pos.Raw.extract.go₂, h2, hne, ↓reduceIte]
    exact congrArg (d :: ·) (extract_go₂ post mid (n + d.utf8Size))

private theorem extract_go₁ (rest : List Char) (hrest : rest ≠ []) (e : String.Pos.Raw) :
    ∀ (pre : List Char) (n : Nat),
      String.Pos.Raw.extract.go₁ (pre ++ rest) ⟨n⟩ ⟨n + byteLen pre⟩ e =
        String.Pos.Raw.extract.go₂ rest ⟨n + byteLen pre⟩ e
  | [], n => by
    obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil hrest
    simp [String.Pos.Raw.extract.go₁, byteLen]
  | d :: pre, n => by
    have hd := d.utf8Size_pos
    have h2 : n + byteLen (d :: pre) = n + d.utf8Size + byteLen pre := by simp [byteLen, Nat.add_assoc]
    have hne : (⟨n⟩ : String.Pos.Raw) ≠ ⟨n + d.utf8Size + byteLen pre⟩ := by simp; omega
    simp only [List.cons_append, String.Pos.Raw.extract.go₁, h2, hne, ↓reduceIte]
    exact extract_go₁ rest hrest e pre (n + d.utf8Size)

private theorem extract_mid (s : String) (pre mid post : List Char) (h : s.toList = pre ++ mid ++ post) :
    String.Pos.Raw.extract s ⟨byteLen pre⟩ ⟨byteLen (pre ++ mid)⟩ = String.ofList mid := by
  unfold String.Pos.Raw.extract
  by_cases hm : mid = []
  · subst hm
    simp
  · have hpos := byteLen_pos hm
    have hlt : ¬ (byteLen pre ≥ byteLen (pre ++ mid)) := by rw [byteLen_append]; omega
    simp only [hlt, ↓reduceIte, h, List.append_assoc]
    have h1 := extract_go₁ (mid ++ post) (by simp [hm]) ⟨byteLen (pre ++ mid)⟩ pre 0
    simp only [Nat.zero_add] at h1
    have h0 : (0 : String.Pos.Raw) = ⟨0⟩ := rfl
    rw [h0, h1, byteLen_append, extract_go₂ post mid (byteLen pre)]

private theorem newline_get : (0 : String.Pos.Raw).get "\n" = '\n' := by decide

private theorem newline_next : (0 : String.Pos.Raw).next "\n" = ⟨1⟩ := by decide

private theorem newline_atEnd : (⟨1⟩ : String.Pos.Raw).atEnd "\n" = true := by decide

private theorem splitOnAux_newline (s : String) :
    ∀ (rest pre mid : List Char) (r : List String), s.toList = pre ++ mid ++ rest → '\n' ∉ mid →
      String.splitOnAux s "\n" ⟨byteLen pre⟩ ⟨byteLen (pre ++ mid)⟩ 0 r =
        r.reverse ++ ((mid ++ rest).splitOn '\n').map String.ofList
  | [], pre, mid, r, h, hmid => by
    rw [String.splitOnAux]
    have hend : (⟨byteLen (pre ++ mid)⟩ : String.Pos.Raw).atEnd s = true := by
      simp [String.Pos.Raw.atEnd, utf8ByteSize_eq, h]
    simp only [hend, ↓reduceIte, extract_mid s pre mid [] h, List.append_nil, List.splitOn_eq_singleton hmid]
    simp
  | c :: rest, pre, mid, r, h, hmid => by
    rw [String.splitOnAux]
    have hend : (⟨byteLen (pre ++ mid)⟩ : String.Pos.Raw).atEnd s = false := by
      have := c.utf8Size_pos
      simp [String.Pos.Raw.atEnd, utf8ByteSize_eq, h, byteLen_append, byteLen]
      omega
    have hget : (⟨byteLen (pre ++ mid)⟩ : String.Pos.Raw).get s = c := by
      have := utf8GetAux_at c rest (pre ++ mid) 0
      simp only [Nat.zero_add] at this
      simp only [String.Pos.Raw.get, h, List.append_assoc] at this ⊢
      exact this
    have hnext : (⟨byteLen (pre ++ mid)⟩ : String.Pos.Raw).next s = ⟨byteLen (pre ++ mid ++ [c])⟩ := by
      rw [String.Pos.Raw.next, hget]
      show (⟨byteLen (pre ++ mid) + c.utf8Size⟩ : String.Pos.Raw) = _
      simp [byteLen_append, byteLen, Nat.add_assoc]
    simp only [hend, Bool.false_eq_true, ↓reduceIte, hget, newline_get, newline_next, newline_atEnd,
      String.Pos.Raw.unoffsetBy_zero, hnext]
    by_cases hc : c = '\n'
    · subst hc
      have hback : (⟨byteLen (pre ++ mid ++ ['\n'])⟩ : String.Pos.Raw).unoffsetBy ⟨1⟩ = ⟨byteLen (pre ++ mid)⟩ := by
        have hsize : '\n'.utf8Size = 1 := by decide
        simp [String.Pos.Raw.unoffsetBy, byteLen_append, byteLen, hsize]
      have ih := splitOnAux_newline s rest (pre ++ mid ++ ['\n']) [] (String.ofList mid :: r)
        (by simp [h]) (by simp)
      rw [List.append_nil] at ih
      simp only [beq_self_eq_true, ↓reduceIte, hback, extract_mid s pre mid ('\n' :: rest) h, ih,
        List.splitOn_append_cons_self_of_not_mem hmid rest]
      simp
    · have ih := splitOnAux_newline s rest pre (mid ++ [c]) r (by simp [h]) (by simp [hmid, Ne.symm hc])
      rw [← List.append_assoc] at ih
      simp only [beq_iff_eq, hc, ↓reduceIte, ih]
      simp

private theorem splitOn_newline (s : String) : s.splitOn "\n" = (s.toList.splitOn '\n').map String.ofList := by
  have h := splitOnAux_newline s s.toList [] [] [] (by simp) (by simp)
  simp only [byteLen, List.append_nil, List.nil_append, List.reverse_nil] at h
  unfold String.splitOn
  simpa using h

private theorem splitOn_ne_nil (s : String) : s.splitOn "\n" ≠ [] := by
  rw [splitOn_newline]
  simp [List.splitOn_ne_nil]

private theorem toList_terminated {β : Type u} (f : β → String) :
    ∀ (xs : List β), (String.join (xs.map fun x => f x ++ "\n")).toList =
      ['\n'].intercalate (xs.map (fun x => (f x).toList) ++ [[]])
  | [] => by simp
  | x :: xs => by
    rw [List.map_cons, List.map_cons, List.cons_append, List.intercalate_cons_of_ne_nil (by simp),
      ← toList_terminated f xs]
    simp

private theorem eq_terminated {β : Type u} (f : β → String) (xs : List β) (s : String)
    (h : s.splitOn "\n" = xs.map f ++ [""]) : s = String.join (xs.map fun x => f x ++ "\n") := by
  rw [splitOn_newline] at h
  have hl : s.toList.splitOn '\n' = xs.map (fun x => (f x).toList) ++ [[]] := by
    have := congrArg (List.map String.toList) h
    simpa [List.map_map, Function.comp_def] using this
  apply String.ext
  rw [toList_terminated, ← hl, List.intercalate_splitOn]

private theorem splitOn_terminated {β : Type u} (f : β → String) (xs : List β)
    (h : ∀ x ∈ xs, '\n' ∉ (f x).toList) :
    (String.join (xs.map fun x => f x ++ "\n")).splitOn "\n" = xs.map f ++ [""] := by
  rw [splitOn_newline, toList_terminated, List.splitOn_intercalate]
  · simp [Function.comp_def]
  · intro l hl
    simp only [List.mem_append, List.mem_map, List.mem_singleton] at hl
    rcases hl with ⟨x, hx, rfl⟩ | rfl
    · exact h x hx
    · simp
  · simp

private theorem except_ok_bind {ε α β : Type _} (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

private theorem except_error_bind {ε α β : Type _} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

private theorem except_map_ok {ε α β : Type _} (f : α → β) (a : α) :
    (f <$> (Except.ok a : Except ε α)) = .ok (f a) := rfl

private theorem except_map_error {ε α β : Type _} (f : α → β) (e : ε) :
    (f <$> (Except.error e : Except ε α)) = .error e := rfl

private theorem except_pure {ε α : Type _} (a : α) : (pure a : Except ε α) = .ok a := rfl

private theorem readLines_ok {α : Type u} (read : String → Except String α) :
    ∀ (lines : List String) (last : String) (number : Nat) (out as : Array α),
      readLines read number out (lines ++ [last]) = .ok as ↔
        last = "" ∧ ∃ bs, lines.mapM read = .ok bs ∧ as = out ++ bs.toArray
  | [], last, number, out, as => by
    by_cases hl : last = ""
    · subst hl
      have he : "".isEmpty = true := String.isEmpty_iff.mpr rfl
      have hm : ([] : List String).mapM read = .ok [] := rfl
      simp only [List.nil_append, readLines, List.isEmpty_nil, Bool.true_and, he, ↓reduceIte, Except.ok.injEq,
        true_and]
      constructor
      · intro h
        exact ⟨[], hm, by simp [h]⟩
      · rintro ⟨bs, hbs, rfl⟩
        rw [hm] at hbs
        cases hbs
        simp
    · simp only [List.nil_append, readLines, List.isEmpty_nil, Bool.true_and, hl, false_and, iff_false]
      cases read last <;> simp [String.isEmpty_iff, hl]
  | l :: lines, last, number, out, as => by
    have hne : (lines ++ [last]).isEmpty = false := by simp
    simp only [List.cons_append, readLines, hne, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    cases hr : read l with
    | error e => simp [List.mapM_cons, hr, except_error_bind]
    | ok a =>
      simp only
      rw [readLines_ok read lines last (number + 1) (out.push a) as]
      cases hm : lines.mapM read with
      | error e => simp [List.mapM_cons, hr, hm, except_ok_bind, except_map_error]
      | ok bs => simp [List.mapM_cons, hr, hm, except_ok_bind, except_map_ok]

private theorem mapM_ok_sound {α : Type u} {read : String → Except String α} {g : α → String} {P : α → Prop}
    (hg : ∀ l b, read l = .ok b → g b = l ∧ P b) :
    ∀ (lines : List String) (bs : List α), lines.mapM read = .ok bs → lines = bs.map g ∧ ∀ b ∈ bs, P b
  | [], bs, h => by
    have hnil : ([] : List String).mapM read = .ok [] := rfl
    rw [hnil] at h
    cases h
    simp
  | l :: lines, bs, h => by
    cases hr : read l with
    | error e => simp [List.mapM_cons, hr, except_error_bind] at h
    | ok b =>
      cases hm : lines.mapM read with
      | error e => simp [List.mapM_cons, hr, hm, except_ok_bind, except_map_error] at h
      | ok rest =>
        simp only [List.mapM_cons, hr, hm, except_ok_bind, except_pure, Except.ok.injEq] at h
        subst h
        obtain ⟨hrest, hP⟩ := mapM_ok_sound hg lines rest hm
        refine ⟨by rw [List.map_cons, (hg l b hr).1, ← hrest], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (hg l x hr).2
        · exact hP x hx

private theorem mapM_map_ok {α : Type u} {read : String → Except String α} {f : α → String} :
    ∀ (xs : List α), (∀ x ∈ xs, read (f x) = .ok x) → (xs.map f).mapM read = .ok xs
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    have hxs := mapM_map_ok xs (fun y hy => h y (by simp [hy]))
    simp [List.mapM_cons, hx, hxs, except_ok_bind, except_map_ok]

private theorem readLines_sound {α : Type u} (read : String → Except String α) (g : α → String) (P : α → Prop)
    (hg : ∀ l b, read l = .ok b → g b = l ∧ P b) (s : String) (as : Array α)
    (h : readLines read 0 #[] (s.splitOn "\n") = .ok as) :
    (∀ a ∈ as.toList, P a) ∧ s = String.join (as.toList.map fun a => g a ++ "\n") := by
  rw [← List.dropLast_concat_getLast (splitOn_ne_nil s), readLines_ok] at h
  obtain ⟨hlast, bs, hbs, rfl⟩ := h
  obtain ⟨hlines, hP⟩ := mapM_ok_sound hg _ bs hbs
  have hbs' : (#[] ++ bs.toArray).toList = bs := by simp
  rw [hbs']
  refine ⟨hP, eq_terminated g bs s ?_⟩
  rw [← hlines, ← hlast]
  exact (List.dropLast_concat_getLast _).symm

private theorem foldl_renderLines (l : List Value) (out : String) :
    l.foldl (fun out v => (Value.renderTo out v).push '\n') out =
      out ++ String.join (l.map fun v => v.render ++ "\n") := by
  induction l generalizing out with
  | nil => simp
  | cons v l ih =>
    rw [List.foldl_cons, ih]
    apply String.ext
    simp [String.toList_append, String.toList_push, Value.renderTo_toList out v, Value.render]

private theorem render_parse {v : Value} (h : v.Valid) : Value.parse v.render = .ok v :=
  render_parse_of_floats (floatsReadBack ofScientificRounds) v h

private theorem decode_ok_encode {α : Type u} [ToValue α] [FromValue α] {s : String} {a : α}
    (h : decode s = .ok a) : encode a = s := by
  unfold decode at h
  split at h
  · cases h
  · rename_i v hv
    split at h
    · cases h
    · split at h
      · rename_i same
        cases h
        unfold encode
        rw [Value.eq_of_beq _ _ same]
        exact (parse_sound s v hv).1
      · cases h

private theorem no_newline (v : Value) : '\n' ∉ v.render.toList := fun hc =>
  absurd (printable_render v '\n' hc) (by decide)

theorem renderLines_eq (vs : Array Value) :
    Value.renderLines vs = String.join (vs.toList.map fun v => v.render ++ "\n") := by
  rw [Value.renderLines, ← Array.foldl_toList, foldl_renderLines, String.empty_append]

theorem parseLines_fixed (s : String) (vs : Array Value) :
    Value.parseLines s = .ok vs ↔ (∀ v ∈ vs.toList, v.Valid) ∧ Value.renderLines vs = s := by
  constructor
  · intro h
    obtain ⟨hvalid, htext⟩ := readLines_sound Value.parse Value.render Value.Valid
      (fun l b hb => parse_sound l b hb) s vs h
    exact ⟨hvalid, by rw [renderLines_eq]; exact htext.symm⟩
  · rintro ⟨hvalid, rfl⟩
    unfold Value.parseLines
    rw [renderLines_eq, splitOn_terminated Value.render vs.toList (fun v _ => no_newline v), readLines_ok]
    exact ⟨rfl, vs.toList, mapM_map_ok vs.toList (fun v hv => render_parse (hvalid v hv)), by simp⟩

theorem encodeLines_eq {α : Type u} [ToValue α] (as : Array α) :
    encodeLines as = Value.renderLines (as.map toValue) := by
  rw [encodeLines, Value.renderLines, Array.foldl_map]

theorem decodeLines_text {α : Type u} [ToValue α] [FromValue α] (s : String) (as : Array α)
    (h : decodeLines s = .ok as) : encodeLines as = s := by
  obtain ⟨-, htext⟩ := readLines_sound decode encode (fun _ => True)
    (fun _ _ hb => ⟨decode_ok_encode hb, trivial⟩) s as h
  rw [htext, encodeLines_eq, renderLines_eq]
  simp [encode, Function.comp_def]

theorem decodeLines_encode {α : Type u} [ToValue α] [FromValue α]
    (lawful : ∀ a : α, fromValue? (toValue a) = .ok a) (valid : ∀ a : α, (toValue a).Valid) (as : Array α) :
    decodeLines (encodeLines as) = .ok as := by
  have htext : encodeLines as = String.join (as.toList.map fun a => encode a ++ "\n") := by
    rw [encodeLines_eq, renderLines_eq]
    simp [encode, Function.comp_def]
  unfold decodeLines
  rw [htext, splitOn_terminated encode as.toList (fun a _ => no_newline (toValue a)), readLines_ok]
  exact ⟨rfl, as.toList,
    mapM_map_ok as.toList (fun a _ => decode_encode_of_rounds ofScientificRounds lawful valid a), by simp⟩

theorem renderLines_eq_rejects_empty :
    ¬ ∀ (vs : Array Value), (fun (_ : Array Value) => "") vs = String.join (vs.toList.map fun v => v.render ++ "\n") := by
  intro h
  have := congrArg String.toList (h #[.null])
  simp at this

theorem parseLines_fixed_rejects_empty :
    ¬ ∀ (s : String) (vs : Array Value),
      (fun (_ : String) => (Except.ok #[] : Except String (Array Value))) s = .ok vs ↔
        (∀ v ∈ vs.toList, v.Valid) ∧ (fun (_ : Array Value) => "") vs = s := by
  intro h
  exact absurd ((h "x" #[]).mp rfl).2 (by decide)

theorem encodeLines_eq_rejects_constant :
    ¬ ∀ {α : Type u} [ToValue α] (as : Array α),
      (fun {β : Type u} [ToValue β] (_ : Array β) => "x") as = (fun (_ : Array Value) => "") (as.map toValue) := by
  intro h
  exact absurd (@h PUnit ⟨fun _ => .null⟩ #[]) (by decide)

theorem decodeLines_text_rejects_empty :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α] (s : String) (as : Array α),
      (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (Except.ok #[] : Except String (Array β))) s = .ok as →
        (fun {β : Type u} [ToValue β] (_ : Array β) => "x") as = s := by
  intro h
  exact absurd (@h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ "" #[] rfl) (by decide)

theorem decodeLines_encode_rejects_failure :
    ¬ ∀ {α : Type u} [ToValue α] [FromValue α], (∀ a : α, fromValue? (toValue a) = .ok a) →
      (∀ a : α, (toValue a).Valid) → ∀ (as : Array α),
        (fun {β : Type u} [ToValue β] [FromValue β] (_ : String) => (Except.error "" : Except String (Array β)))
          ((fun {β : Type u} [ToValue β] (_ : Array β) => "") as) = .ok as := by
  intro h
  cases @h PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ (fun _ => rfl) (fun _ => rfl) #[]

theorem decodeLines_text_applies :
    ∃ (α : Type u) (_ : ToValue α) (_ : FromValue α) (s : String) (as : Array α), decodeLines s = .ok as :=
  ⟨PUnit, ⟨fun _ => .null⟩, ⟨fun _ => .ok ⟨⟩⟩, @encodeLines PUnit ⟨fun _ => .null⟩ #[], #[],
    @decodeLines_encode PUnit ⟨fun _ => .null⟩ ⟨fun _ => .ok ⟨⟩⟩ (fun _ => rfl) (fun _ => rfl) #[]⟩

end ExactJSON
