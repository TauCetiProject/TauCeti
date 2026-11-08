/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Reciprocal series of consecutive integers

The geometric series with ratio `(n + 2)⁻¹` starting at the exponent two sums to the difference
`(n + 1)⁻¹ - (n + 2)⁻¹` of consecutive reciprocals, and these differences telescope to a series
with sum one.

## Main results

* `TauCeti.hasSum_inv_add_two_pow_add_two`: the geometric series with ratio `(n + 2)⁻¹`, from the
  exponent two.
* `TauCeti.hasSum_inv_add_one_sub_inv_add_two`: the telescoping series of reciprocal differences.
-/

public section

open Filter Finset

namespace TauCeti

/-- The geometric series with ratio `(n + 2)⁻¹` starting at the exponent two sums to the
difference of consecutive reciprocals `(n + 1)⁻¹ - (n + 2)⁻¹`. -/
theorem hasSum_inv_add_two_pow_add_two (n : ℕ) :
    HasSum (fun k : ℕ ↦ (((n : ℝ) + 2)⁻¹) ^ (k + 2))
      (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) := by
  have h := (hasSum_geometric_of_lt_one
    (by positivity : 0 ≤ ((n : ℝ) + 2)⁻¹) (by
      rw [inv_lt_one₀ (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith)).mul_right (((n : ℝ) + 2)⁻¹ ^ 2)
  simp only [pow_add] at ⊢
  convert h using 1
  field_simp
  ring_nf
  field_simp
  ring

/-- The reciprocal differences `(n + 1)⁻¹ - (n + 2)⁻¹` telescope to a series with sum one. -/
theorem hasSum_inv_add_one_sub_inv_add_two :
    HasSum (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹) 1 := by
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ by
    apply sub_nonneg.mpr
    gcongr
    norm_num) _).mpr ?_
  have hsum (N : ℕ) :
      (∑ n ∈ range N, (((n : ℝ) + 1)⁻¹ - ((n : ℝ) + 2)⁻¹)) =
        1 - ((N : ℝ) + 1)⁻¹ := by
    simpa [Nat.cast_add, add_assoc, one_add_one_eq_two] using
      (sum_range_sub' (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) N)
  simp_rw [hsum]
  simpa using tendsto_const_nhds.sub
    (tendsto_inv_atTop_zero.comp (tendsto_atTop_mono
      (fun n : ℕ ↦ le_add_of_nonneg_right (zero_le_one : (0 : ℝ) ≤ 1))
      tendsto_natCast_atTop_atTop))

end TauCeti
