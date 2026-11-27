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
The closed ball `{x | v x ≤ γ}` is also recorded as the underlying set of Mathlib's additive
subgroup `Valuation.leAddSubgroup`.

## Main results

* `Valuation.map_add_pow_le_max`: `v (x + y) ^ n ≤ max (v x ^ n) (v y ^ n)`.
* `Valuation.map_natCast_le_one`: `v n ≤ 1` for every natural number `n`.
* `Valuation.coe_leAddSubgroup`: the subgroup `v.leAddSubgroup γ` is the set `{x | v x ≤ γ}`.
* `Valuation.map_mul_mul_inv_le`: if `v a ≤ v b`, then `v (a * c * b⁻¹) ≤ v c`.
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

/-- The additive subgroup `v.leAddSubgroup γ` is the closed ball `{x | v x ≤ γ}`. -/
@[simp]
theorem coe_leAddSubgroup {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    (γ : Γ₀) : (v.leAddSubgroup γ : Set R) = {x | v x ≤ γ} :=
  Set.ext fun _ ↦ mem_leAddSubgroup_iff

/-- If `v a ≤ v b` in a division ring, then `v (a * c * b⁻¹) ≤ v c`. -/
theorem map_mul_mul_inv_le {K Γ₀ : Type*} [DivisionRing K] [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation K Γ₀) {a b c : K} (hab : v a ≤ v b) :
    v (a * c * b⁻¹) ≤ v c := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  · rw [map_mul, map_mul, map_inv₀, mul_right_comm]
    have hpos : 0 < v b := pos_iff_ne_zero.mpr (by simp [hb])
    have hratio : v a * (v b)⁻¹ ≤ 1 := (mul_inv_le_iff₀ hpos).mpr (by simpa using hab)
    simpa using mul_le_mul_of_nonneg_right hratio zero_le

end Valuation

end
