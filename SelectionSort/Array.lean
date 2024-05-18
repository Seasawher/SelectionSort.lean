/-
# 選択ソート
選択ソートは，次のような手順で行われるソートアルゴリズムです．

-/
import Mathlib.Tactic

variable {α : Type} [LinearOrder α]

/-- 配列 `arr` が与えられたとき, `arr[i]` から `arr` の最後尾までの部分のうち
最小の要素 `arr[min]` を探し，それを `arr[i]` と交換する -/
def selectionSortLoop (arr : Array α) (i : Fin arr.size) : Array α :=
  if i ≥ arr.size then
    arr
  else
    sorry
