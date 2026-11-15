/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Splitting a square of indices by the gap between them

Fix a gap `N`. The pairs `(k, l)` of indices below `n` fall into three classes: those with
`k + N < l`, those with `l + N < k`, and those with `|k - l| ≤ N`. Sorting the terms of a double
sum `∑_{k, l < n} c k l` into these classes is the combinatorial step of Bony's decomposition of a
product of two Littlewood–Paley partial sums into two paraproducts and a resonant term.

## Main results

* `Finset.sum_range_sum_range_split_gap`: the double sum over `range n × range n` is the sum over
  the pairs with `k < l - N`, the pairs with `l < k - N` and the pairs with `|k - l| ≤ N`.
-/

public section

namespace Finset

/-- **Splitting a double sum by the gap between the indices.** For every gap `N`, the double sum
`∑_{k, l < n} c k l` is the sum of the terms with `k + N < l`, those with `l + N < k`, and those
with `|k - l| ≤ N`. -/
theorem sum_range_sum_range_split_gap {M : Type*} [AddCommMonoid M] (N n : ℕ)
    (c : ℕ → ℕ → M) :
    ∑ k ∈ range n, ∑ l ∈ range n, c k l =
      ∑ l ∈ range n, ∑ k ∈ range (l - N), c k l + ∑ k ∈ range n, ∑ l ∈ range (k - N), c k l +
        ∑ k ∈ range n, ∑ l ∈ (range n).filter (fun l ↦ l ≤ k + N ∧ k ≤ l + N), c k l := by
  have hsplit : ∀ k ∈ range n, ∑ l ∈ range n, c k l =
      ∑ l ∈ (range n).filter (fun l ↦ k + N < l), c k l + ∑ l ∈ range (k - N), c k l +
        ∑ l ∈ (range n).filter (fun l ↦ l ≤ k + N ∧ k ≤ l + N), c k l := fun k hk ↦ by
    rw [mem_range] at hk
    rw [← sum_filter_add_sum_filter_not (range n) (fun l ↦ k + N < l),
      ← sum_filter_add_sum_filter_not ((range n).filter fun l ↦ ¬k + N < l) (fun l ↦ l + N < k),
      ← add_assoc]
    congr 1
    · congr 1
      refine sum_congr ?_ fun _ _ ↦ rfl
      ext l
      simp only [mem_filter, mem_range]
      omega
    · refine sum_congr ?_ fun _ _ ↦ rfl
      ext l
      simp only [mem_filter, mem_range]
      omega
  rw [sum_congr rfl hsplit, sum_add_distrib, sum_add_distrib]
  congr 2
  refine sum_comm' fun k l ↦ ?_
  simp only [mem_range, mem_filter]
  omega

end Finset
