/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.BigOperators.Intervals
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

* `Finset.prod_pow_sub_one`: factoring `q ^ (∑ i ∈ s, f i)` out of `∏ i ∈ s, (q ^ f i - 1)`.
* `Finset.sum_range_add_mul_add_div_two`: the increments of a quadratic along a uniform grid sum to
  the increment of the quadratic.
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
`t ↦ t * u + t ^ 2 * X / 2` along the grid `k * a` sum, over `k < n` with `n * a = 1`, to the value
`u + X / 2` of the quadratic at `1`. -/
theorem sum_range_add_mul_add_div_two {K : Type*} [Field K] [CharZero K] {a u X : K} {n : ℕ}
    (hna : (n : K) * a = 1) :
    ∑ k ∈ Finset.range n, (a * u + (k * a + a / 2) * a * X) = u + X / 2 := by
  have hsum : ∀ m : ℕ, ∑ k ∈ Finset.range m, (a * u + (k * a + a / 2) * a * X) =
      m * a * u + (m * a) ^ 2 * X / 2 := fun m => by
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [hsum, hna]
  ring

end Finset
