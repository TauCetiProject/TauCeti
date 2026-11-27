/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Two-sided bounds for `log (1 + 1 / a)`

For `a > 0` write `y = 1 / (2 a + 1)`. Mathlib's series
`log (1 + a⁻¹) = Σ_{k ≥ 0} 2 y^{2k+1} / (2k + 1)` (`Real.hasSum_log_one_add_inv`) has nonnegative
terms, which gives two elementary bounds:

* keeping its first two terms, `2 y + 2 y³ / 3 ≤ log (1 + a⁻¹)`;
* dropping the factors `1 / (2k + 1)`, `log (1 + a⁻¹) ≤ 2 y / (1 - y²) = (2a + 1) / (2a (a + 1))`.

At `a = n` the upper bound is the trapezoidal rule for `∫_n^{n+1} dt / t`, and the lower bound
agrees with `log (1 + 1 / n)` up to `O(n⁻⁵)`. Summed over `n`, they give two-sided bounds of the
right order `1 / (2n)` for `harmonic n - log n - γ`.

## Main results

* `Real.log_one_add_inv_le`: `log (1 + a⁻¹) ≤ (2a + 1) / (2a (a + 1))` for `a > 0`.
* `Real.two_div_add_two_div_le_log_one_add_inv`:
  `2 / (2a + 1) + 2 / (3 (2a + 1)³) ≤ log (1 + a⁻¹)` for `a > 0`.
-/

public section

namespace Real

/-- The trapezoidal upper bound: for `a > 0`, `log (1 + 1 / a) ≤ (2a + 1) / (2a (a + 1))`. -/
theorem log_one_add_inv_le {a : ℝ} (ha : 0 < a) :
    log (1 + a⁻¹) ≤ (2 * a + 1) / (2 * a * (a + 1)) := by
  set y : ℝ := 1 / (2 * a + 1) with hy
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by rw [hy, div_lt_one (by positivity)]; linarith
  have hy2 : y ^ 2 < 1 := by nlinarith
  have hg : HasSum (fun k : ℕ ↦ 2 * y * (y ^ 2) ^ k) (2 * y * (1 - y ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one (by positivity) hy2).mul_left (2 * y)
  have hle := hasSum_le (fun k : ℕ ↦ ?_) (hasSum_log_one_add_inv ha) hg
  · have h1 : (2 * a + 1) ≠ 0 := by positivity
    have h2 : 1 - y ^ 2 = 4 * a * (a + 1) / (2 * a + 1) ^ 2 := by
      rw [hy]
      field_simp
      ring
    refine hle.trans_eq ?_
    rw [h2, hy]
    field_simp
    norm_num
  · rw [← hy, pow_succ, pow_mul]
    have hk : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [k.cast_nonneg (α := ℝ)]
    have : 0 ≤ (y ^ 2) ^ k * y := by positivity
    nlinarith

/-- The first two terms of the series for `log (1 + 1 / a)`: for `a > 0`,
`2 / (2a + 1) + 2 / (3 (2a + 1)³) ≤ log (1 + 1 / a)`. -/
theorem two_div_add_two_div_le_log_one_add_inv {a : ℝ} (ha : 0 < a) :
    2 / (2 * a + 1) + 2 / (3 * (2 * a + 1) ^ 3) ≤ log (1 + a⁻¹) := by
  have h := sum_le_hasSum (Finset.range 2) (fun k _ ↦ by positivity) (hasSum_log_one_add_inv ha)
  refine le_of_eq_of_le ?_ h
  have h1 : (2 * a + 1) ≠ 0 := by positivity
  norm_num [Finset.sum_range_succ]
  field_simp

end Real
