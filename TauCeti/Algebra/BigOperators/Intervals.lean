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

A sum `∑ k ∈ Ico m (n + 1), f k` whose summands split as `f m = β m`, `f n = γ n`, and
`f k = γ k + β k` for `m < k < n` regroups as the sum over `m ≤ k < n` of the adjacent pairs
`β k + γ (k + 1)`. The codomain is any additive commutative monoid. In a not necessarily
associative ring, a constant summed over the `n - 2` indices `1 ≤ k < n - 1` is `(n - 2)` times it.

## Main results

* `Finset.sum_Ico_eq_sum_Ico_add`: the regrouping of `∑ k ∈ Ico m (n + 1), f k` into the pairs
  `β k + γ (k + 1)`.
* `Finset.sum_Ico_one_sub_one_const`: `∑ _k ∈ Ico 1 (n - 1), c = (n - 2) * c` for `2 ≤ n`.
-/

public section

namespace Finset

/-- If `m < n`, the summands `f m = β m`, `f n = γ n`, and `f k = γ k + β k` for
`m < k < n` regroup as the adjacent pairs `β k + γ (k + 1)` over `m ≤ k < n`. -/
theorem sum_Ico_eq_sum_Ico_add {M : Type*} [AddCommMonoid M] {f β γ : ℕ → M} {m n : ℕ}
    (hmn : m < n) (hfirst : f m = β m) (hmid : ∀ k ∈ Ico (m + 1) n, f k = γ k + β k)
    (hlast : f n = γ n) :
    ∑ k ∈ Ico m (n + 1), f k = ∑ k ∈ Ico m n, (β k + γ (k + 1)) := by
  -- peel off the endpoint summands
  have hf : ∑ k ∈ Ico m (n + 1), f k = f m + ∑ k ∈ Ico (m + 1) n, f k + f n := by
    rw [sum_eq_sum_Ico_succ_bot (by omega), sum_Ico_succ_top (by omega), add_assoc]
  -- peel off the first `β`-summand
  have hβ : ∑ k ∈ Ico m n, β k = β m + ∑ k ∈ Ico (m + 1) n, β k :=
    sum_eq_sum_Ico_succ_bot hmn β
  -- shift the `γ`-summands down by one and peel off the last one
  have hγ : ∑ k ∈ Ico m n, γ (k + 1) = ∑ k ∈ Ico (m + 1) n, γ k + γ n := by
    rw [sum_Ico_add' γ, sum_Ico_succ_top (by omega : m + 1 ≤ n)]
  simp only [hf, sum_congr rfl hmid, sum_add_distrib, hβ, hγ, hfirst, hlast]
  abel

/-- A constant summed over the `n - 2` indices `1 ≤ k < n - 1` is `(n - 2)` times it. -/
theorem sum_Ico_one_sub_one_const {R : Type*} [NonAssocRing R] {n : ℕ} (hn : 2 ≤ n) (c : R) :
    ∑ _k ∈ Ico 1 (n - 1), c = ((n : R) - 2) * c := by
  rw [sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.sub_sub, Nat.cast_sub hn, Nat.cast_ofNat]

end Finset
