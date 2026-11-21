/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Field.GeomSum

/-!
# Reciprocal series of consecutive integers

The geometric series with ratio `(n + 2)⁻¹` starting at the exponent two sums to the difference
`(n + 1)⁻¹ - (n + 2)⁻¹` of consecutive reciprocals, and its finite partial sums on `2 ≤ k ≤ M` for
any base `p ≠ 1` are bounded by `1 / (p * (p - 1))`. Summing the consecutive-reciprocal differences
over `n` telescopes to a series with sum one.

## Main results

* `TauCeti.sum_Icc_inv_pow_le`: for `p ≠ 1`, the partial sum of `p ^ (-k)` on `2 ≤ k ≤ M` is at
  most `1 / (p * (p - 1))`.
* `TauCeti.hasSum_inv_add_two_pow_add_two`: the geometric series with ratio `(n + 2)⁻¹`, from the
  exponent two.
* `TauCeti.hasSum_inv_add_one_sub_inv_add_two`: the telescoping series of reciprocal differences.
-/

public section

open Filter Finset

namespace TauCeti

/-- For `p ≠ 1`, the higher-power reciprocals `p ^ (-k)` on `2 ≤ k ≤ M` sum to at most
`1 / (p * (p - 1))` (and to `0 = 1 / (0 * (0 - 1))` when `p = 0`). -/
theorem sum_Icc_inv_pow_le {p : ℕ} (hp : p ≠ 1) (M : ℕ) :
    ∑ k ∈ Icc 2 M, ((p : ℝ) ^ k)⁻¹ ≤ 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
  rw [← Ico_add_one_right_eq_Icc]
  simp_rw [← inv_pow]
  rcases eq_or_ne p 0 with rfl | hp0
  · exact (geom_sum_Ico_le_of_lt_one (by norm_num) (by norm_num)).trans_eq (by norm_num)
  have hp1 : (1 : ℝ) < p := mod_cast Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨hp0, hp⟩
  refine (geom_sum_Ico_le_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)).trans_eq ?_
  have hp_sub : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp1.ne'
  field_simp

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
