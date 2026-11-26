/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import TauCeti.Algebra.Order.BigOperators.Sum.Min

/-!
# The Gale–Ryser theorem for conjugate column sums

Let `μ : ι → ℕ` and `ν : κ → ℕ` be finite families of natural numbers. A family of finite sets
`S : κ → Finset ℕ` is a `0`-`1` matrix with rows indexed by `κ` and columns by `ℕ`: row `l` has
its ones in the columns `S l`. This file characterizes when there is such a matrix with row sums
`#(S l) = ν l` and column sums `#{l | i ∈ S l} = #{j | i < μ j}`, the column lengths of the Young
diagram with rows `μ`: this happens exactly when `μ` and `ν` have the same total and every
truncated sum `∑ j, min k (μ j)` is at most `∑ l, min k (ν l)`.

The truncated sum `∑ j, min k (μ j)` counts the boxes in the first `k` columns of the diagram of
`μ`, so the condition says that the column sums are dominated by the conjugate of the row sums.
This is the Gale–Ryser theorem for a sequence of column sums which is already the conjugate of a
partition. For partitions, the condition is dominance of `ν` by `μ`
(`Nat.Partition.ofSums_dominates_ofSums_iff`).

Necessity is a double count: the ones in the first `k` columns number at most `min k (ν l)` in
row `l`. Sufficiency is the greedy construction: fill column `0` with ones in the
`#{j | 0 < μ j}` rows of largest `ν l`, then remove the first column of `μ` and recurse.

For a discrete valuation ring with maximal ideal `𝔪`, such a matrix describes a filtration of
`∏ l, A ⧸ 𝔪 ^ ν l` with semisimple graded pieces of dimensions `#{j | i < μ j}`, by the
submodules `∏ l, 𝔪 ^ #{a ∈ S l | a < i} (A ⧸ 𝔪 ^ ν l)`.

## Main results

* `TauCeti.sum_min_le_of_card_eq_card_filter_mem`, `TauCeti.sum_eq_of_card_eq_card_filter_mem`:
  the column sums of a `0`-`1` matrix are dominated by the conjugate of its row sums, with the same
  total.
* `TauCeti.exists_finset_card_eq_card_filter_mem`: the greedy construction of a `0`-`1` matrix
  with row sums `ν` and column sums the conjugate of `μ`.
* `TauCeti.exists_finset_card_eq_card_filter_mem_iff`: such a matrix exists if and only if the
  totals agree and the truncated sums of `μ` are at most those of `ν`.

## References

* D. Gale, *A theorem on flows in networks*, Pacific J. Math. 7 (1957), 1073–1082.
* H. J. Ryser, *Combinatorial properties of matrices of zeros and ones*, Canad. J. Math. 9
  (1957), 371–377.
-/

public section

open Finset

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
/-- In a finite set `s` with `c ≤ #s`, some `c` elements carry the largest values of `f`. -/
private theorem exists_subset_card_eq_forall_le (f : κ → ℕ) (s : Finset κ) {c : ℕ}
    (hc : c ≤ #s) : ∃ C ⊆ s, #C = c ∧ ∀ l ∈ s, l ∉ C → ∀ l' ∈ C, f l ≤ f l' := by
  classical
  induction c with
  | zero => exact ⟨∅, empty_subset _, card_empty, fun _ _ _ _ h ↦ absurd h (notMem_empty _)⟩
  | succ c ih =>
    obtain ⟨C, hCs, hC, htop⟩ := ih (Nat.le_of_succ_le hc)
    have hne : (s \ C).Nonempty := by
      rw [← card_pos, card_sdiff_of_subset hCs]
      omega
    obtain ⟨m, hm, hmax⟩ := exists_max_image (s \ C) f hne
    rw [mem_sdiff] at hm
    refine ⟨insert m C, insert_subset hm.1 hCs, by rw [card_insert_of_notMem hm.2, hC], ?_⟩
    intro l hl hlC l' hl'
    rw [mem_insert, not_or] at hlC
    rcases mem_insert.1 hl' with rfl | hl'
    · exact hmax l (mem_sdiff.2 ⟨hl, hlC.2⟩)
    · exact htop l hl hlC.2 l' hl'

/-- If the columns of a `0`-`1` matrix with rows `S l` have the lengths `#{j | i < μ j}`, then the
truncated sum `∑ j, min k (μ j)` counts the ones of the matrix in its first `k` columns. -/
private theorem sum_min_eq_sum_card_filter_mem {μ : ι → ℕ} {S : κ → Finset ℕ}
    (hcol : ∀ i, #{l | i ∈ S l} = #{j | i < μ j}) (k : ℕ) :
    ∑ j, min k (μ j) = ∑ l, #{i ∈ range k | i ∈ S l} := by
  classical
  rw [sum_min_eq_sum_range_card_filter_lt]
  simp_rw [← hcol, card_filter]
  exact sum_comm

/-- **Gale–Ryser, necessity.** If a `0`-`1` matrix with rows `S l` has row sums `ν l` and column
sums `#{j | i < μ j}`, then `∑ j, min k (μ j) ≤ ∑ l, min k (ν l)` for every `k`: its first `k`
columns contain at most `min k (ν l)` ones of row `l`. -/
theorem sum_min_le_of_card_eq_card_filter_mem {μ : ι → ℕ} {ν : κ → ℕ} {S : κ → Finset ℕ}
    (hS : ∀ l, #(S l) = ν l) (hcol : ∀ i, #{l | i ∈ S l} = #{j | i < μ j}) (k : ℕ) :
    ∑ j, min k (μ j) ≤ ∑ l, min k (ν l) := by
  rw [sum_min_eq_sum_card_filter_mem hcol]
  refine sum_le_sum fun l _ ↦ le_min ?_ ?_
  · exact (card_filter_le _ _).trans (card_range k).le
  · exact (hS l) ▸ card_le_card fun i hi ↦ (mem_filter.1 hi).2

/-- The totals of the row sums and of the column sums of a `0`-`1` matrix agree. -/
theorem sum_eq_of_card_eq_card_filter_mem {μ : ι → ℕ} {ν : κ → ℕ} {S : κ → Finset ℕ}
    (hS : ∀ l, #(S l) = ν l) (hcol : ∀ i, #{l | i ∈ S l} = #{j | i < μ j}) :
    ∑ j, μ j = ∑ l, ν l := by
  classical
  -- Truncate at a column `k` beyond every part of `μ` and every column used by `S`.
  obtain ⟨n, hn⟩ := exists_nat_subset_range (univ.biUnion S)
  set k := max n (univ.sup μ)
  have h := sum_min_eq_sum_card_filter_mem hcol k
  rw [sum_congr rfl fun j _ ↦ min_eq_right ((le_sup (mem_univ j)).trans (le_max_right _ _)),
    sum_congr rfl fun l _ ↦ (?_ : #{i ∈ range k | i ∈ S l} = ν l)] at h
  · exact h
  · rw [← hS l, filter_mem_eq_inter, inter_eq_right.2]
    exact fun i hi ↦ range_subset_range.2 (le_max_left _ _) (hn (mem_biUnion.2 ⟨l, mem_univ l, hi⟩))

section Sufficiency

/-! ### The greedy step

Column `0` receives its ones in a set `C` of `#{j | 0 < μ j}` rows carrying the largest values of
`ν`. Removing that column leaves the families `μ j - 1` and `ν l - [l ∈ C]`. -/

variable {μ : ι → ℕ} {ν : κ → ℕ} {C : Finset κ} [DecidablePred (· ∈ C)]

/-- The greedy step preserves the truncated-sum inequalities: if the rows `C`, with
`#C = #{j | 0 < μ j}`, carry the largest positive values of `ν`, then the families `μ j - 1` and
`ν l - [l ∈ C]` again satisfy `∑ j, min k (μ j - 1) ≤ ∑ l, min k (ν l - [l ∈ C])`. -/
private theorem sum_min_le_of_greedy (hCpos : ∀ l ∈ C, 0 < ν l)
    (htop : ∀ l, 0 < ν l → l ∉ C → ∀ l' ∈ C, ν l ≤ ν l') (hC : #C = #{j | 0 < μ j})
    (h : ∀ k, ∑ j, min k (μ j) ≤ ∑ l, min k (ν l)) (k : ℕ) :
    ∑ j, min k (μ j - 1) ≤ ∑ l, min k (if l ∈ C then ν l - 1 else ν l) := by
  classical
  by_cases hu : ∃ l ∉ C, k < ν l
  · -- Some row outside `C` exceeds `k`, so every row of `C` does: truncating at `k` does not see
    -- the boxes removed from `ν`.
    obtain ⟨l₀, hl₀C, hl₀⟩ := hu
    have hCk (l : κ) (hl : l ∈ C) : k < ν l := hl₀.trans_le (htop l₀ (by omega) hl₀C l hl)
    calc ∑ j, min k (μ j - 1) ≤ ∑ j, min k (μ j) :=
          sum_le_sum fun j _ ↦ min_le_min_left _ (Nat.sub_le _ _)
      _ ≤ ∑ l, min k (ν l) := h k
      _ = ∑ l, min k (if l ∈ C then ν l - 1 else ν l) := sum_congr rfl fun l _ ↦ by
          split_ifs with hl
          · have := hCk l hl
            omega
          · rfl
  · -- Every row outside `C` is at most `k`, so truncating at `k + 1` sees exactly one extra box in
    -- each row of `C`, and one extra box in each nonzero row of `μ`.
    simp only [not_exists, not_and, not_lt] at hu
    have hμ : ∑ j, min (k + 1) (μ j) = ∑ j, min k (μ j - 1) + #{j | 0 < μ j} := by
      rw [card_filter, ← sum_add_distrib]
      exact sum_congr rfl fun j _ ↦ by split_ifs <;> omega
    have hν : ∑ l, min (k + 1) (ν l) =
        ∑ l, min k (if l ∈ C then ν l - 1 else ν l) + #{l | l ∈ C} := by
      rw [card_filter, ← sum_add_distrib]
      refine sum_congr rfl fun l _ ↦ ?_
      by_cases hl : l ∈ C
      · have := hCpos l hl
        simp only [hl, ↓reduceIte]
        omega
      · have := hu l hl
        simp only [hl, ↓reduceIte]
        omega
    have := h (k + 1)
    rw [hμ, hν, filter_mem_eq_inter, univ_inter, hC] at this
    omega

/-- The greedy step reversed: a `0`-`1` matrix for the families `μ j - 1` and
`ν l - [l ∈ C]`, shifted by one column and completed by ones in column `0` on the rows `C`, is a
matrix for `μ` and `ν`. -/
private theorem exists_of_greedy (hCpos : ∀ l ∈ C, 0 < ν l) (hC : #C = #{j | 0 < μ j})
    {S' : κ → Finset ℕ} (hS' : ∀ l, #(S' l) = if l ∈ C then ν l - 1 else ν l)
    (hcol' : ∀ i, #{l | i ∈ S' l} = #{j | i < μ j - 1}) :
    ∃ S : κ → Finset ℕ, (∀ l, #(S l) = ν l) ∧ ∀ i, #{l | i ∈ S l} = #{j | i < μ j} := by
  classical
  let sh : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  let S : κ → Finset ℕ := fun l ↦ if l ∈ C then insert 0 ((S' l).map sh) else (S' l).map sh
  have hzero (l : κ) : 0 ∈ S l ↔ l ∈ C := by
    by_cases hl : l ∈ C <;> simp [S, sh, hl]
  have hsucc (l : κ) (i : ℕ) : i + 1 ∈ S l ↔ i ∈ S' l := by
    by_cases hl : l ∈ C <;> simp [S, sh, hl]
  refine ⟨S, fun l ↦ ?_, fun i ↦ ?_⟩
  · have h := hS' l
    by_cases hl : l ∈ C
    · have := hCpos l hl
      simp only [S, hl, ↓reduceIte] at h ⊢
      rw [card_insert_of_notMem (by simp [sh]), card_map, h]
      omega
    · simp only [S, hl, ↓reduceIte] at h ⊢
      rw [card_map, h]
  · rcases i with _ | i
    · rw [filter_congr fun l _ ↦ hzero l, filter_mem_eq_inter, univ_inter, hC]
    · rw [filter_congr fun l _ ↦ hsucc l i, hcol' i]
      exact congrArg card (filter_congr fun j _ ↦ by omega)

end Sufficiency

/-- **Gale–Ryser, sufficiency.** If `μ` and `ν` have the same total and
`∑ j, min k (μ j) ≤ ∑ l, min k (ν l)` for every `k`, there is a `0`-`1` matrix with rows `S l`
whose row sums are `ν l` and whose column sums are the column lengths `#{j | i < μ j}` of the
Young diagram with rows `μ`. -/
theorem exists_finset_card_eq_card_filter_mem (μ : ι → ℕ) (ν : κ → ℕ)
    (hsum : ∑ j, μ j = ∑ l, ν l) (h : ∀ k, ∑ j, min k (μ j) ≤ ∑ l, min k (ν l)) :
    ∃ S : κ → Finset ℕ, (∀ l, #(S l) = ν l) ∧ ∀ i, #{l | i ∈ S l} = #{j | i < μ j} := by
  classical
  -- Induction on a bound `m` for the parts of `μ`, removing the first column at each step.
  obtain ⟨m, hm⟩ : ∃ m, ∀ j, μ j ≤ m := ⟨univ.sup μ, fun j ↦ le_sup (mem_univ j)⟩
  induction m generalizing μ ν with
  | zero =>
    have hμ (j : ι) : μ j = 0 := Nat.le_zero.1 (hm j)
    have hν : ∀ l, ν l = 0 := by simpa [hμ, sum_eq_zero_iff] using hsum.symm
    exact ⟨fun _ ↦ ∅, fun l ↦ by simp [hν], fun i ↦ by simp [hμ]⟩
  | succ m ih =>
    -- Column `0` needs `#{j | 0 < μ j}` ones, at most the number of nonzero rows of `ν`.
    have hc : #{j | 0 < μ j} ≤ #{l | 0 < ν l} := by
      have h₁ := h 1
      rw [← zero_add 1, sum_min_add_one, sum_min_add_one] at h₁
      simpa using h₁
    obtain ⟨C, hCs, hC, htop⟩ := exists_subset_card_eq_forall_le ν _ hc
    have hCpos (l : κ) (hl : l ∈ C) : 0 < ν l := (mem_filter.1 (hCs hl)).2
    -- Removing the first column lowers both totals by `#C`.
    have hsum' : ∑ j, (μ j - 1) = ∑ l, if l ∈ C then ν l - 1 else ν l := by
      have h₁ : ∑ j, μ j = ∑ j, (μ j - 1) + #{j | 0 < μ j} := by
        rw [card_filter, ← sum_add_distrib]
        exact sum_congr rfl fun j _ ↦ by split_ifs <;> omega
      have h₂ : ∑ l, ν l = ∑ l, (if l ∈ C then ν l - 1 else ν l) + #{l | l ∈ C} := by
        rw [card_filter, ← sum_add_distrib]
        refine sum_congr rfl fun l _ ↦ ?_
        by_cases hl : l ∈ C
        · have := hCpos l hl
          simp only [hl, ↓reduceIte]
          omega
        · simp only [hl, ↓reduceIte]
          omega
      rw [filter_mem_eq_inter, univ_inter] at h₂
      omega
    obtain ⟨S', hS', hcol'⟩ := ih (fun j ↦ μ j - 1) (fun l ↦ if l ∈ C then ν l - 1 else ν l)
      hsum' (sum_min_le_of_greedy hCpos (fun l hl ↦ htop l (mem_filter.2 ⟨mem_univ _, hl⟩)) hC h)
      fun j ↦ by have := hm j; omega
    exact exists_of_greedy hCpos hC hS' hcol'

/-- **The Gale–Ryser theorem for conjugate column sums.** There is a `0`-`1` matrix with rows
`S l`, row sums `ν l` and column sums the column lengths `#{j | i < μ j}` of the Young diagram with
rows `μ` if and only if `μ` and `ν` have the same total and `∑ j, min k (μ j) ≤ ∑ l, min k (ν l)`
for every `k`. -/
theorem exists_finset_card_eq_card_filter_mem_iff (μ : ι → ℕ) (ν : κ → ℕ) :
    (∃ S : κ → Finset ℕ, (∀ l, #(S l) = ν l) ∧ ∀ i, #{l | i ∈ S l} = #{j | i < μ j}) ↔
      ∑ j, μ j = ∑ l, ν l ∧ ∀ k, ∑ j, min k (μ j) ≤ ∑ l, min k (ν l) :=
  ⟨fun ⟨_, hS, hcol⟩ ↦ ⟨sum_eq_of_card_eq_card_filter_mem hS hcol,
    sum_min_le_of_card_eq_card_filter_mem hS hcol⟩,
    fun ⟨hsum, h⟩ ↦ exists_finset_card_eq_card_filter_mem μ ν hsum h⟩

end TauCeti
