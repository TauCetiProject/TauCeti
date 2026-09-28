/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Valuation.Basic

/-!
# The valuation of a difference of powers

For a valuation `v` on a commutative ring and elements `x`, `y` with `v x ≤ c` and `v y ≤ c`,
the factorization `x ^ n - y ^ n = (x - y) * ∑ j < n, x ^ j * y ^ (n - 1 - j)` and the
ultrametric inequality give

`v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1)`.

This is the estimate that makes a power series with small coefficients contract differences of
its arguments, for instance the logarithm on the deep units of a local field.
-/

public section

namespace Valuation

variable {R Γ₀ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ₀]

/-- If `v x ≤ c` and `v y ≤ c`, then `v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1)`. -/
theorem map_pow_sub_pow_le (v : Valuation R Γ₀) {x y : R} {c : Γ₀} (hx : v x ≤ c)
    (hy : v y ≤ c) (n : ℕ) :
    v (x ^ n - y ^ n) ≤ v (x - y) * c ^ (n - 1) := by
  rw [← geom_sum₂_mul, map_mul, mul_comm]
  gcongr
  refine v.map_sum_le fun j hj => ?_
  have hj : j ≤ n - 1 := Nat.le_sub_one_of_lt (Finset.mem_range.mp hj)
  rw [map_mul, map_pow, map_pow, ← Nat.add_sub_cancel' hj, pow_add, Nat.add_sub_cancel_left]
  gcongr <;> exact zero_le

end Valuation
