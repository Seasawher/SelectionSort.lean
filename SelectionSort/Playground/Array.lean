import Mathlib.Tactic

variable {α : Type} [LinearOrder α]

def selectionSortLoop (arr : Array α) (i : Fin arr.size) : Array α :=
  if i ≥ arr.size then
    arr
  else
    sorry
