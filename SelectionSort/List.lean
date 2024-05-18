import Mathlib.Tactic

variable {α : Type} [LinearOrder α]

open List

def List.minErased {l : List α} (pos : l.length > 0) : List α :=
  let μ : α := minimum_of_length_pos pos
  l.erase μ

theorem List.minErased_length {l : List α} (pos : l.length > 0)
    : (minErased pos).length + 1 = l.length := by
  exact length_erase_add_one <| minimum_of_length_pos_mem pos

def List.min_first (l : List α) : List α :=
  match l.minimum with
  | ⊤ => []
  | some μ => μ :: l.erase μ

theorem List.min_first_length (l : List α) : (min_first l).length = l.length := by
  induction l with
  | nil =>
    simp [min_first]
  | cons h t ih =>
    simp [min_first, ih]
    split
    next x μ heq =>
      simp at heq
    next x μ heq =>
      simp only [length_cons, Nat.succ_eq_add_one, add_left_inj]
      sorry

def List.selection_sort (l : List α) : List α :=
  match min_first l with
  | [] => []
  | μ :: rest =>
    have : (min_first l).length = l.length := by sorry
    have : rest.length < l.length := by sorry
    μ :: selection_sort rest
termination_by l.length

-- def List.perm_min_first (l : List α) : l ~ l.min_first := by
--   induction l with
--   | nil =>
--     simp [min_first]
--   | cons h t ih =>
--     by_cases h : 0 < (h :: t).length
--     case pos =>
--       simp [min_first, h]
--       have : h :: t.erase (minimum_of_length_pos h) ~ h :: (minimum_of_length_pos h :: t.erase (minimum_of_length_pos h)) := by
--         exact perm.cons _ ih



-- def List.minFirst_pos {l : List α} (pos : l.length > 0) : 0 < (minFirst pos).length := by
--   exact Nat.zero_lt_succ (l.erase (minimum_of_length_pos pos)).length



example : selection_sort [3, 1, 4, 1, 5, 9, 2, 6, 5, 3, 5] = [1, 1, 2, 3, 3, 4, 5, 5, 5, 6, 9] := by
  first
  | rfl
  | native_decide

-- def List.selection_sort (l : List α) : List α :=
--   if pos : 0 < l.length then
--     let μ := minimum_of_length_pos pos
--     let rest := l.minErased pos

--     -- lemma for termination
--     have : l.length > rest.length := calc
--       l.length = rest.length + 1 := by rw [minErased_length pos]
--       _ > rest.length := by simp_arith

--     μ :: (selection_sort rest)
--   else
--     []
-- termination_by l.length

-- theorem perm_selection_sort (l : List α) : l ~ l.selection_sort := by
--   induction' ih : l.length generalizing l

--   all_goals
--     unfold selection_sort
--     simp_all [ih]

--   case succ n =>
--     set μ := minimum_of_length_pos (_ : 0 < length l)
--     set rest := l.erase μ

--     sorry
--   sorry
  -- case succ n ih =>
  --   sorry

/-- リストから `i` 番目以降の要素を取り出す -/
def _root_.List.slice (l : List α) (i : Nat) : List α :=
  match i, l with
  | 0, _ => l
  | _, [] => []
  | i + 1, _h :: t =>
    List.slice t i

@[simp]
theorem _root_.List.slice_nil (i : Nat) : List.slice ([] : List α) i = [] := by
  cases i <;> rfl

theorem _root_.List.slice_length (l : List α) (i : Nat) : (List.slice l i).length = l.length - i := by
  induction l with
  | nil =>
    simp
  | cons h t ih =>
    sorry

#eval [1, 2, 3, 4, 5].slice 4
#eval [1, 2, 3, 4, 5, 6, 7, 8, 9].slice 2

/-- リスト `List` が与えられたとき, `List[i]` から `List` の最後尾までの部分のうち
最小の要素 `List[min]` を探し，それを `List[i]` と交換する -/
def selectionSortLoop (l : List α) (i : Nat) : List α :=
  if hl : i ≥ l.length then
    l
  else
    match l with
    | [] => []
    | h :: t =>
      let slice := t.slice i
      have : slice.length > 0 := by

        sorry
      sorry
