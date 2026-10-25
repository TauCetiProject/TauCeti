/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Field.Basic

/-!
# Factoring the leading power out of a product of `q ^ k - 1`

For `q ≠ 0` in a field,
`∏ i ∈ s, (q ^ f i - 1) = q ^ (∑ i ∈ s, f i) * ∏ i ∈ s, (1 - (q ^ f i)⁻¹)`. This is how the orders
of the finite classical groups, which are products of factors `q ^ k - 1`, become the normalized
values `∏ (1 - q^{-k})` of local densities.

## Main results

* `Finset.prod_pow_sub_one`: factoring `q ^ (∑ i ∈ s, f i)` out of `∏ i ∈ s, (q ^ f i - 1)`.
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

end Finset
