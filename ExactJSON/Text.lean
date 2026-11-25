module

public import ExactJSON.Render

@[expose] public section

namespace ExactJSON

def escapeList (cs : List Char) : List Char := cs.flatMap fun c => (pushChar "" c).toList

theorem escapeList_nil : escapeList [] = [] := by simp [escapeList]

theorem escapeList_cons (c : Char) (cs : List Char) :
    escapeList (c :: cs) = (pushChar "" c).toList ++ escapeList cs := by
  simp [escapeList]

theorem pushChar_toList (out : String) (c : Char) :
    (pushChar out c).toList = out.toList ++ (pushChar "" c).toList := by
  simp only [pushChar]
  repeat' split
  all_goals simp_all [String.toList_append, String.toList_push]

theorem foldl_pushChar_toList : ∀ (cs : List Char) (out : String),
    (cs.foldl pushChar out).toList = out.toList ++ escapeList cs
  | [], _ => by simp [escapeList]
  | c :: cs, out => by
    rw [List.foldl_cons, foldl_pushChar_toList cs, pushChar_toList, escapeList_cons, List.append_assoc]

theorem pushString_toList (out s : String) :
    (pushString out s).toList = out.toList ++ '"' :: (escapeList s.toList ++ ['"']) := by
  simp [pushString, String.foldl_eq_foldl_toList, String.toList_push, foldl_pushChar_toList]

namespace Value

mutual

theorem renderTo_toList (out : String) : (v : Value) →
    (renderTo out v).toList = out.toList ++ (renderTo "" v).toList
  | .null => by simp [renderTo, String.toList_append]
  | .string s => by simp [renderTo, pushString_toList]
  | .integer n => by simp [renderTo, String.toList_append]
  | .decimal d => by simp [renderTo, String.toList_append]
  | .boolean b => by simp [renderTo, String.toList_append]
  | .array ⟨items⟩ => by
    simp only [renderTo, String.toList_push]
    rw [renderItems_toList (out.push '[') items, renderItems_toList ("".push '[') items]
    simp [String.toList_push]
  | .table ⟨members⟩ => by
    simp only [renderTo, String.toList_push]
    rw [renderMembers_toList (out.push '{') members, renderMembers_toList ("".push '{') members]
    simp [String.toList_push]

theorem renderItems_toList (out : String) : (items : List Value) →
    (renderItems out items).toList = out.toList ++ (renderItems "" items).toList
  | [] => by simp [renderItems]
  | [v] => by simp only [renderItems]; exact renderTo_toList out v
  | v :: w :: rest => by
    have h1 := renderItems_toList ((renderTo out v).push ',') (w :: rest)
    have h2 := renderItems_toList ((renderTo "" v).push ',') (w :: rest)
    have h3 := renderTo_toList out v
    simp only [renderItems]
    rw [h1, h2]
    simp only [String.toList_push, h3]
    simp

theorem renderMembers_toList (out : String) : (members : List (String × Value)) →
    (renderMembers out members).toList = out.toList ++ (renderMembers "" members).toList
  | [] => by simp [renderMembers]
  | [(k, v)] => by
    have h3 := renderTo_toList ((pushString out k).push ':') v
    have h4 := renderTo_toList ((pushString "" k).push ':') v
    simp only [renderMembers]
    rw [h3, h4]
    simp [String.toList_push, pushString_toList]
  | (k, v) :: m :: rest => by
    have h1 := renderMembers_toList ((renderTo ((pushString out k).push ':') v).push ',') (m :: rest)
    have h2 := renderMembers_toList ((renderTo ((pushString "" k).push ':') v).push ',') (m :: rest)
    have h3 := renderTo_toList ((pushString out k).push ':') v
    have h4 := renderTo_toList ((pushString "" k).push ':') v
    simp only [renderMembers]
    rw [h1, h2]
    simp only [String.toList_push, h3, h4, pushString_toList]
    simp

end

def itemsText (items : List Value) : List Char := (renderItems "" items).toList

def membersText (members : List (String × Value)) : List Char := (renderMembers "" members).toList

theorem text_null : (render .null).toList = ['n', 'u', 'l', 'l'] := by decide

theorem text_boolean (b : Bool) :
    (render (.boolean b)).toList = if b then ['t', 'r', 'u', 'e'] else ['f', 'a', 'l', 's', 'e'] := by
  cases b <;> decide

theorem text_string (s : String) : (render (.string s)).toList = '"' :: (escapeList s.toList ++ ['"']) := by
  simp [render, renderTo, pushString_toList]

theorem text_array (items : List Value) :
    (render (.array ⟨items⟩)).toList = '[' :: (itemsText items ++ [']']) := by
  have h := renderItems_toList ("".push '[') items
  simp only [render, renderTo, String.toList_push]
  rw [h]
  simp [itemsText]

theorem text_table (members : List (String × Value)) :
    (render (.table ⟨members⟩)).toList = '{' :: (membersText members ++ ['}']) := by
  have h := renderMembers_toList ("".push '{') members
  simp only [render, renderTo, String.toList_push]
  rw [h]
  simp [membersText]

theorem itemsText_singleton (v : Value) : itemsText [v] = (render v).toList := by
  simp [itemsText, renderItems, render]

theorem itemsText_cons (v w : Value) (rest : List Value) :
    itemsText (v :: w :: rest) = (render v).toList ++ ',' :: itemsText (w :: rest) := by
  have h := renderItems_toList ((renderTo "" v).push ',') (w :: rest)
  simp only [itemsText, renderItems]
  rw [h]
  simp [String.toList_push, render]

def memberText (key : String) (v : Value) : List Char :=
  '"' :: (escapeList key.toList ++ '"' :: ':' :: (render v).toList)

theorem membersText_singleton (key : String) (v : Value) : membersText [(key, v)] = memberText key v := by
  have h := renderTo_toList ((pushString "" key).push ':') v
  simp only [membersText, renderMembers, memberText]
  rw [h]
  simp [String.toList_push, pushString_toList, render]

theorem membersText_cons (key : String) (v : Value) (m : String × Value) (rest : List (String × Value)) :
    membersText ((key, v) :: m :: rest) = memberText key v ++ ',' :: membersText (m :: rest) := by
  have h1 := renderMembers_toList ((renderTo ((pushString "" key).push ':') v).push ',') (m :: rest)
  have h2 := renderTo_toList ((pushString "" key).push ':') v
  simp only [membersText, renderMembers, memberText]
  rw [h1]
  simp only [String.toList_push, h2, pushString_toList]
  simp [render]

end Value

end ExactJSON
