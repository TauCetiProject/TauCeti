/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Basic

/-!
# Elementary bounds for valuations

Two elementary consequences of the ultrametric inequality `v (x + y) ≤ max (v x) (v y)`: it
persists after raising both sides to a power, and every natural number has value at most `1`.

## Main results

* `Valuation.map_add_pow_le_max`: `v (x + y) ^ n ≤ max (v x ^ n) (v y ^ n)`.
* `Valuation.map_natCast_le_one`: `v n ≤ 1` for every natural number `n`.
* `Valuation.map_sub_of_distinct_val`: when `v x ≠ v y`, `v (x - y) = max (v x) (v y)`.
-/

public section

namespace Valuation

variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)

/-- The ultrametric inequality raised to a power: `v (x + y) ^ n ≤ max (v x ^ n) (v y ^ n)`. -/
theorem map_add_pow_le_max (x y : R) (n : ℕ) : v (x + y) ^ n ≤ max (v x ^ n) (v y ^ n) :=
  (pow_le_pow_left₀ zero_le (v.map_add x y) n).trans_eq (max_pow_of_nonneg zero_le zero_le n)

/-- Every natural number has value at most `1`. -/
theorem map_natCast_le_one (n : ℕ) : v (n : R) ≤ 1 := by
  simpa using v.map_sum_le (s := Finset.range n) (f := fun _ ↦ 1) fun _ _ ↦ v.map_one.le

/-- When `x` and `y` have distinct valuations, `v (x - y) = max (v x) (v y)`. -/
theorem map_sub_of_distinct_val {x y : R} (h : v x ≠ v y) : v (x - y) = max (v x) (v y) := by
  rw [sub_eq_add_neg, v.map_add_of_distinct_val (by simpa [v.map_neg] using h), v.map_neg]

end Valuation

end
