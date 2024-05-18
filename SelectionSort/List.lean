import Mathlib.Tactic

variable {α : Type} [LinearOrder α]

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
