/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import TauCeti.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum.Basic

/-!
# Finite products and sums in a field

## Factoring the leading power out of a product of `q ^ k - 1`

For `q ≠ 0` in a field,
`∏ i ∈ s, (q ^ f i - 1) = q ^ (∑ i ∈ s, f i) * ∏ i ∈ s, (1 - (q ^ f i)⁻¹)`. This is how the orders
of the finite classical groups, which are products of factors `q ^ k - 1`, become the normalized
values `∏ (1 - q^{-k})` of local densities.

## Main results

* `Finset.sum_range_natCast`, `Finset.sum_range_natCast_sq`: sums of naturals and their squares in
  a division ring where `2 ≠ 0` (and, for the squares, also `3 ≠ 0`).
* `Finset.prod_pow_sub_one`: factoring `q ^ (∑ i ∈ s, f i)` out of `∏ i ∈ s, (q ^ f i - 1)`.
* `Finset.sum_range_add_mul_add_div_two`: the increments of a quadratic along a uniform grid sum to
  the increment of the quadratic from `0` to the end of the grid.
-/

public section

namespace Finset

/-- **Factoring the leading power out of a product of `q ^ k - 1`.** For `q ≠ 0` in a field,
`∏ i ∈ s, (q ^ f i - 1) = q ^ (∑ i ∈ s, f i) * ∏ i ∈ s, (1 - (q ^ f i)⁻¹)`. -/
theorem prod_pow_sub_one {K ι : Type*} [Field K] {q : K} (hq : q ≠ 0) (s : Finset ι)
    (f : ι → ℕ) :
    ∏ i ∈ s, (q ^ f i - 1) = q ^ (∑ i ∈ s, f i) * ∏ i ∈ s, (1 - (q ^ f i)⁻¹) := by
  rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [mul_sub, mul_one, mul_inv_cancel₀ (pow_ne_zero _ hq)]

/-- The expected increments `a * u + (k * a + a / 2) * a * X` of the quadratic
`t ↦ t * u + t ^ 2 * X / 2` along the grid `k * a` sum, over `k < n`, to the increment
`n * a * u + (n * a) ^ 2 * X / 2` of the quadratic from `0` to `n * a`. -/
theorem sum_range_add_mul_add_div_two {K : Type*} [Field K] [CharZero K] (a u X : K) (n : ℕ) :
    ∑ k ∈ Finset.range n, (a * u + (k * a + a / 2) * a * X) =
      n * a * u + (n * a) ^ 2 * X / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The sum of the natural numbers below `n`, cast into a division ring where `2 ≠ 0`. -/
theorem sum_range_natCast {K : Type*} [DivisionRing K] [NeZero (2 : K)] (n : ℕ) :
    ∑ r ∈ range n, (r : K) = n * (n - 1) / 2 :=
  (eq_div_iff two_ne_zero).2 (sum_range_natCast_mul_two n)

/-- The sum of the squares of natural numbers below `n`, in a division ring where `2 ≠ 0` and
`3 ≠ 0`. -/
theorem sum_range_natCast_sq {K : Type*} [DivisionRing K] [NeZero (2 : K)] [NeZero (3 : K)]
    (n : ℕ) : ∑ r ∈ range n, (r : K) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero two_ne_zero three_ne_zero
  exact (eq_div_iff h6).2 (sum_range_natCast_sq_mul_six n)

end Finset
