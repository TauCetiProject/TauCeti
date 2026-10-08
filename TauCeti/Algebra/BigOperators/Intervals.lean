/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Abel

/-!
# Sums over intervals of natural numbers

A sum `∑ k ∈ range (N + 3), f k` whose summands split as `f 0 = 0`, `f 1 = β 1`,
`f k = γ k + β k` for `2 ≤ k ≤ N + 1` and `f (N + 2) = γ (N + 2)` regroups as the sum over
`1 ≤ k ≤ N + 1` of the adjacent pairs `β k + γ (k + 1)`. The codomain is any additive commutative
monoid. A constant summed over the `n - 2` indices `1 ≤ k < n - 1` is `(n - 2)` times it.

## Main results

* `Finset.sum_range_eq_sum_Ico_add`: the regrouping of `∑ k ∈ range (N + 3), f k` into the pairs
  `β k + γ (k + 1)`.
* `Finset.sum_Ico_one_sub_one_const`: `∑ _k ∈ Ico 1 (n - 1), c = (n - 2) * c` for `2 ≤ n`.
-/

public section

namespace Finset

/-- If the summands of a sum over `range (N + 3)` are `f 0 = 0`, `f 1 = β 1`,
`f k = γ k + β k` for `2 ≤ k < N + 2` and `f (N + 2) = γ (N + 2)`, the sum regroups as the sum of
the adjacent pairs `β k + γ (k + 1)` over `1 ≤ k < N + 2`. -/
theorem sum_range_eq_sum_Ico_add {M : Type*} [AddCommMonoid M] {f β γ : ℕ → M} {N : ℕ}
    (h₀ : f 0 = 0) (h₁ : f 1 = β 1) (hmid : ∀ k ∈ Ico 2 (N + 2), f k = γ k + β k)
    (hlast : f (N + 2) = γ (N + 2)) :
    ∑ k ∈ range (N + 3), f k = ∑ k ∈ Ico 1 (N + 2), (β k + γ (k + 1)) := by
  -- peel off the summands at `0`, `1` and `N + 2`
  have hf : ∑ k ∈ range (N + 3), f k = f 0 + f 1 + ∑ k ∈ Ico 2 (N + 2), f k + f (N + 2) := by
    rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega), sum_eq_sum_Ico_succ_bot (by omega),
      sum_Ico_succ_top (by omega : 2 ≤ N + 2), add_assoc, add_assoc]
  -- peel off the first `β`-summand
  have hβ : ∑ k ∈ Ico 1 (N + 2), β k = β 1 + ∑ k ∈ Ico 2 (N + 2), β k :=
    sum_eq_sum_Ico_succ_bot (by omega) β
  -- shift the `γ`-summands down by one and peel off the last one
  have hγ : ∑ k ∈ Ico 1 (N + 2), γ (k + 1) = ∑ k ∈ Ico 2 (N + 2), γ k + γ (N + 2) := by
    rw [sum_Ico_add' γ, sum_Ico_succ_top (by omega : 2 ≤ N + 2)]
  simp only [hf, sum_congr rfl hmid, sum_add_distrib, hβ, hγ, h₀, h₁, hlast]
  abel

/-- A constant summed over the `n - 2` indices `1 ≤ k < n - 1` is `(n - 2)` times it. -/
theorem sum_Ico_one_sub_one_const {R : Type*} [Ring R] {n : ℕ} (hn : 2 ≤ n) (c : R) :
    ∑ _k ∈ Ico 1 (n - 1), c = ((n : R) - 2) * c := by
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.sub_sub, Nat.cast_sub hn, Nat.cast_ofNat]

end Finset
