import Mathlib.Tactic

variable {α : Type} [LinearOrder α]

namespace List

open List

def min_first (l : List α) : List α :=
  match l.minimum with
  | ⊤ => []
  | some μ =>
    μ :: l.erase μ

@[simp]
theorem min_first_nil : min_first ([] : List α) = [] := by rfl

@[simp]
theorem min_first_iff_nil (l : List α) : min_first l = [] ↔ l = [] := by
  cases l <;> simp [min_first]
  split <;> simp_all

theorem min_first_length (l : List α) : (min_first l).length = l.length := by
  induction l with
  | nil => simp
  | cons h t ih =>
    simp [min_first, ih]
    split
    next heq =>
      simp at heq
    next x μ heq =>
      simp only [length_cons, Nat.succ_eq_add_one, add_left_inj]
      have mem : μ ∈ (h :: t) := minimum_mem heq
      exact length_erase_of_mem mem

theorem perm_min_first (l : List α) : l ~ min_first l := by
  match l with
  | [] => simp
  | h :: t =>
    simp [min_first]
    split
    next x μ heq =>
      simp at heq
    next x μ heq =>
      apply perm_cons_erase
      exact minimum_mem heq

def selection_sort (l : List α) : List α :=
  match h : min_first l with
  | [] => []
  | μ :: rest =>
    -- lemma for termination
    have _decrease : l.length > rest.length := calc
      l.length = (min_first l).length := by rw [min_first_length l]
      _ = rest.length + 1 := by rw [h]; rfl
      _ > rest.length := by simp_arith

    μ :: selection_sort rest
termination_by l.length

@[simp]
theorem selection_sort_nil : selection_sort ([] : List α) = [] := by rfl

theorem perm_selection_sort (l : List α) : l ~ selection_sort l := by
  induction l using selection_sort.induct with

  | case1 l h =>
    simp_all [h]

  | case2 l μ rest hμ hdec ih =>
    rw [selection_sort]
    split
    next heq =>
      simp_all [heq]
    sorry
