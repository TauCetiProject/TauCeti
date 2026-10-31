/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.Group.Indicator

/-!
# Divergence of ordered sums and products over the primes

Mathlib's `not_summable_one_div_on_primes` says that the reciprocals of the primes are not
summable. This file restates the divergence for the ordered cutoffs `p ≤ n` used for Euler
products, with the primes in an arbitrary finite set `T` deleted:

* the partial sums `∑ p ≤ n, p ∉ T, 1 / p` tend to infinity;
* hence, since `(1 - x)⁻¹ ≥ exp x` for `x < 1`, so do the partial Euler products
  `∏ p ≤ n, p ∉ T, (1 - 1 / p)⁻¹` of the Riemann zeta function at `s = 1`.

The deleted set `T` accommodates the Euler products of a trivial Dirichlet character, which omit
the primes dividing the level.

## Main results

* `Nat.tendsto_sum_primesLE_filter_notMem_inv_atTop`: the partial sums of `1 / p` diverge.
* `Nat.tendsto_prod_primesLE_filter_notMem_one_sub_inv_inv_atTop`: the partial Euler products
  `∏ (1 - 1 / p)⁻¹` diverge.
-/

public section

open Filter Finset

namespace Nat

/-- **The sum of the reciprocals of the primes diverges along ordered cutoffs.** For every finite
set `T`, the partial sums `∑ p ≤ n, p ∉ T, 1 / p` tend to infinity. -/
theorem tendsto_sum_primesLE_filter_notMem_inv_atTop (T : Finset ℕ) :
    Tendsto (fun n ↦ ∑ p ∈ primesLE n with p ∉ T, (p : ℝ)⁻¹) atTop atTop := by
  have hall : Tendsto (fun n ↦ ∑ p ∈ primesLE n, (p : ℝ)⁻¹) atTop atTop := by
    have h := (not_summable_iff_tendsto_nat_atTop_of_nonneg fun n ↦
      Set.indicator_nonneg (fun m _ ↦ by positivity) n).mp not_summable_one_div_on_primes
    refine (h.comp (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
    simp [primesLE_eq_filter_range, sum_filter, Set.indicator_apply]
  refine tendsto_atTop_mono (fun n ↦ ?_)
    (tendsto_atTop_add_const_right _ (-∑ p ∈ T, (p : ℝ)⁻¹) hall)
  have hT : ∑ p ∈ primesLE n with p ∈ T, (p : ℝ)⁻¹ ≤ ∑ p ∈ T, (p : ℝ)⁻¹ :=
    sum_le_sum_of_subset_of_nonneg (fun p hp ↦ (mem_filter.mp hp).2) fun _ _ _ ↦ by positivity
  rw [← sum_filter_add_sum_filter_not (primesLE n) (· ∈ T)]
  linarith

/-- **The Euler product of the Riemann zeta function diverges at `s = 1`.** For every finite set
`T`, the partial Euler products `∏ p ≤ n, p ∉ T, (1 - 1 / p)⁻¹` tend to infinity. -/
theorem tendsto_prod_primesLE_filter_notMem_one_sub_inv_inv_atTop (T : Finset ℕ) :
    Tendsto (fun n ↦ ∏ p ∈ primesLE n with p ∉ T, (1 - (p : ℝ)⁻¹)⁻¹) atTop atTop := by
  refine tendsto_atTop_mono (fun n ↦ ?_)
    (Real.tendsto_exp_atTop.comp (tendsto_sum_primesLE_filter_notMem_inv_atTop T))
  rw [Function.comp_apply, Real.exp_sum]
  refine prod_le_prod₀ (fun _ _ ↦ (Real.exp_pos _).le) fun p hp ↦ ?_
  have hp1 : (1 : ℝ) < p := mod_cast (prime_of_mem_primesLE (mem_filter.mp hp).1).one_lt
  have hpos : 0 < 1 - (p : ℝ)⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1)
  simpa [Real.exp_neg] using inv_anti₀ hpos (Real.one_sub_le_exp_neg (p : ℝ)⁻¹)

end Nat
