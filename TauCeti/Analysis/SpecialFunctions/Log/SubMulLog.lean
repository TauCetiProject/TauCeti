/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The function `x ↦ x - ρ log x`

For `ρ ≥ 0` the function `x ↦ x - ρ log x` is convex on `(0, ∞)`, with derivative `1 - ρ / x`;
for `ρ > 0` it has its minimum at `x = ρ`. It is the building block of the first integrals of
the SIR epidemic model and of the Lotka–Volterra equations. This file proves its tangent line
inequality from `Real.log_le_sub_one_of_pos`, and that it is strictly decreasing on `(0, ρ]` and
strictly increasing on `[ρ, ∞)`.

## Main results

* `Real.sub_mul_one_sub_div_le_sub_mul_log_sub_sub_mul_log`: the tangent line inequality at `a`.
* `Real.sub_mul_one_sub_div_lt_sub_mul_log_sub_sub_mul_log`: its strict form for `b ≠ a`, `ρ > 0`.
* `Real.strictAntiOn_sub_mul_log`: `x ↦ x - ρ log x` is strictly decreasing on `(0, ρ]`.
* `Real.strictMonoOn_sub_mul_log`: for `ρ ≥ 0`, `x ↦ x - ρ log x` is strictly increasing on
  `[ρ, ∞)`.
-/

public section

open Set

namespace Real

/-- The tangent line inequality for the convex function `x ↦ x - ρ log x` at `a`. -/
theorem sub_mul_one_sub_div_le_sub_mul_log_sub_sub_mul_log {ρ a b : ℝ} (hρ : 0 ≤ ρ) (ha : 0 < a)
    (hb : 0 < b) : (b - a) * (1 - ρ / a) ≤ (b - ρ * log b) - (a - ρ * log a) := by
  have hlog := log_le_sub_one_of_pos (div_pos hb ha)
  rw [log_div hb.ne' ha.ne'] at hlog
  have key : ρ * (log b - log a) ≤ ρ * (b / a - 1) := mul_le_mul_of_nonneg_left hlog hρ
  have hexp : (b - a) * (1 - ρ / a) = b - a - ρ * (b / a - 1) := by
    field_simp
  rw [hexp]
  linarith

/-- The strict tangent line inequality for `x ↦ x - ρ log x` at `a`, for `ρ > 0` and `b ≠ a`. -/
theorem sub_mul_one_sub_div_lt_sub_mul_log_sub_sub_mul_log {ρ a b : ℝ} (hρ : 0 < ρ) (ha : 0 < a)
    (hb : 0 < b) (hab : b ≠ a) : (b - a) * (1 - ρ / a) < (b - ρ * log b) - (a - ρ * log a) := by
  have hlog := log_lt_sub_one_of_pos (div_pos hb ha) (mt (div_eq_one_iff_eq ha.ne').1 hab)
  rw [log_div hb.ne' ha.ne'] at hlog
  have key : ρ * (log b - log a) < ρ * (b / a - 1) := mul_lt_mul_of_pos_left hlog hρ
  have hexp : (b - a) * (1 - ρ / a) = b - a - ρ * (b / a - 1) := by
    field_simp
  rw [hexp]
  linarith

/-- The function `x ↦ x - ρ log x` is strictly decreasing on `(0, ρ]`. -/
theorem strictAntiOn_sub_mul_log (ρ : ℝ) : StrictAntiOn (fun x ↦ x - ρ * log x) (Ioc 0 ρ) := by
  intro x hx y hy hxy
  -- The tangent line at `y` puts the value at `x < y ≤ ρ` strictly above the value at `y`.
  have hnonpos : 1 - ρ / y ≤ 0 := by
    rw [sub_nonpos, one_le_div hy.1]
    exact hy.2
  linarith [sub_mul_one_sub_div_lt_sub_mul_log_sub_sub_mul_log (hy.1.trans_le hy.2) hy.1 hx.1
    hxy.ne, mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hxy.le) hnonpos]

/-- For `ρ ≥ 0`, the function `x ↦ x - ρ log x` is strictly increasing on `[ρ, ∞)`. -/
theorem strictMonoOn_sub_mul_log {ρ : ℝ} (hρ : 0 ≤ ρ) :
    StrictMonoOn (fun x ↦ x - ρ * log x) (Ici ρ) := by
  rcases hρ.eq_or_lt with rfl | hρ
  · intro x _ y _ hxy
    simpa using hxy
  intro x hx y _ hxy
  -- The tangent line at `ρ ≤ x < y` puts the value at `y` strictly above the value at `x`.
  have hx₀ : 0 < x := hρ.trans_le hx
  have hnonneg : 0 ≤ 1 - ρ / x := by
    rw [sub_nonneg, div_le_one hx₀]
    exact hx
  linarith [sub_mul_one_sub_div_lt_sub_mul_log_sub_sub_mul_log hρ hx₀ (hx₀.trans hxy) hxy.ne',
    mul_nonneg (sub_nonneg.2 hxy.le) hnonneg]

end Real
