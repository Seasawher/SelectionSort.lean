import Mathlib.Tactic

universe u

open List

-- `α` は線形順序を持つ
variable {α : Type u} [LinearOrder α]

/--
  選択ソート.
  `List.` を名前に付けることにより，リスト `l` に対して `l.selection_sort` で実行できるようになる
-/
def List.selection_sort (l : List α) : List α :=
  if hl : 0 < l.length then
    let μ : α := minimum_of_length_pos hl

    -- `μ` はリストの要素
    have mem : μ ∈ l := by
      apply minimum_mem
      simp_all only [coe_minimum_of_length_pos, μ]

    let rest := l.erase μ

    -- 停止性を示すための補題
    have : l.length > rest.length := calc
      l.length
      _ = rest.length + 1 := by rw [← length_erase_add_one mem]
      _ > rest.length := by linarith

    μ :: (selection_sort rest)
  else
    []
  -- 再帰呼び出しのたびにリストの長さが短くなるので，有限回で停止する
  termination_by l.length

/-- 選択ソートが返すリストは，元のリストと要素の順番だけしか異ならない -/
theorem perm_selection_sort (l : List α) : l ~ selection_sort l := by
  -- リスト `l` の長さに対する帰納法を使う
  induction' ih : l.length generalizing l

  -- `selection_sort` を展開する
  all_goals
    unfold selection_sort
    simp_all [ih]

  -- リストの長さが `n + 1` であるとき
  case succ n IH =>
    -- ゴールが複雑で見づらいので変数を導入する
    set μ := minimum_of_length_pos (_ : 0 < length l)
    set rest := l.erase μ

    -- `μ` が `l` の要素であることを再度示す
    have mem : μ ∈ l := by
      apply minimum_mem
      simp_all only [coe_minimum_of_length_pos, μ]

    -- `rest` の長さについての補題を再度示す
    have rlen : rest.length = n := by
      convert List.length_erase_of_mem mem
      simp only [ih, Nat.pred_succ]

    -- 帰納法の仮定により，`selection_sort rest ~ rest` が言える
    have hr : selection_sort rest ~ rest := by
      exact? says
        exact Perm.symm (IH rest rlen)

    -- 置換の推移性により，`l ~ μ :: rest` を示せばいい
    suffices l ~ μ :: rest from by
      apply this.trans
      simp only [perm_cons, hr.symm]

    -- `List.erase` の性質から示せる
    exact perm_cons_erase mem

/-- selection sort が返すリストは，並び替え済み -/
theorem sorted_selection_sort (l : List α) : Sorted (· ≤ ·) l.selection_sort := by
  induction' ih : l.length generalizing l

  all_goals
    unfold selection_sort
    simp_all [ih]

  case succ n IH =>
    -- ゴールが複雑で見づらいので変数を導入する
    set μ := minimum_of_length_pos (_ : 0 < length l)
    set rest := l.erase μ

    -- `rest` は `l` の部分集合
    have rsub : rest ⊆ l := by
      exact? says
        exact erase_subset μ l

    -- `selection_sort` が置換を返すことを利用する
    have rperm : selection_sort rest ~ rest := by
      exact? says
        exact Perm.symm (perm_selection_sort rest)

    -- `selection_sort rest` は `l` の部分集合
    have subh : selection_sort rest ⊆ l := by
      exact? says
        exact (Perm.subset_congr_left (id (Perm.symm rperm))).mp rsub

    constructor
    · show ∀ (b : α), b ∈ selection_sort rest → minimum l ≤ ↑b
      intro b hb
      exact? says
        exact minimum_le_of_mem' (subh hb)
    · show Sorted (· ≤ ·) (selection_sort rest)
      apply IH rest

      -- `μ` が `l` の要素であることを再度示す(3回目)
      have mem : μ ∈ l := by
        apply minimum_mem
        simp_all only [coe_minimum_of_length_pos, rest, μ]

      -- あとは `rest` の長さが `n` であることを示すだけ
      convert List.length_erase_of_mem mem
      simp only [ih, Nat.pred_succ]
