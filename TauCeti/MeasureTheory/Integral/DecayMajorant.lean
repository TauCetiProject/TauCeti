/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Integrals of functions with a rescaled polynomial-decay majorant

On a finite-dimensional real normed space `E` of dimension `d` with an additive Haar measure `μ`,
the function `w ↦ (1 + ‖w‖) ^ (-(d + 1))` is integrable. Translating it to the centre `x₀` and
dilating it to the scale `R > 0` multiplies its integral by `R ^ d`. Hence a function bounded by
`D (1 + ‖x₀ - w‖ / R) ^ (-(d + 1))` has lower integral at most `D R ^ d ∫ (1 + ‖w‖) ^ (-(d + 1))`.
This is the form in which row and column bounds for Schur's test are obtained from off-diagonal
decay of an integral kernel at scale `R`.

## Main declarations

* `TauCeti.lintegral_le_of_le_inv_one_add_norm_div_pow`: the bound above.
-/

public section

open MeasureTheory Module
open scoped ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- A function bounded by `D (1 + ‖x₀ - w‖ / R) ^ (-(d + 1))`, where `d` is the dimension, has
lower integral at most `D R ^ d ∫ (1 + ‖w‖) ^ (-(d + 1)) dw`. -/
theorem lintegral_le_of_le_inv_one_add_norm_div_pow {R D : ℝ} (hR : 0 < R) (hD : 0 ≤ D) (x₀ : E)
    {f : E → ℝ≥0∞}
    (hf : ∀ w, f w ≤ ENNReal.ofReal (D * ((1 + ‖x₀ - w‖ / R) ^ (finrank ℝ E + 1))⁻¹)) :
    ∫⁻ w, f w ∂μ ≤
      ENNReal.ofReal (D * (∫ w, ((1 + ‖w‖) ^ (finrank ℝ E + 1))⁻¹ ∂μ) * R ^ finrank ℝ E) := by
  set g : E → ℝ := fun w ↦ D * ((1 + ‖w‖ / R) ^ (finrank ℝ E + 1))⁻¹
  -- `g` is integrable, as a rescaling of `(1 + ‖w‖) ^ (-(d + 1))`.
  have hg : Integrable g μ := by
    have h := (integrable_one_add_norm (μ := μ) (r := finrank ℝ E + 1) (by simp)).comp_smul
      (inv_ne_zero hR.ne')
    refine (h.const_mul D).congr (ae_of_all _ fun w ↦ ?_)
    simp only [g, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR]
    rw [Real.rpow_neg (by positivity), ← Nat.cast_one, ← Nat.cast_add, Real.rpow_natCast,
      inv_mul_eq_div]
  -- Its integral is `D R ^ d ∫ (1 + ‖w‖) ^ (-(d + 1)) dw`, by the change of variables `w ↦ R⁻¹ w`.
  have hint : ∫ w, g w ∂μ = D * (∫ w, ((1 + ‖w‖) ^ (finrank ℝ E + 1))⁻¹ ∂μ) * R ^ finrank ℝ E := by
    have h := Measure.integral_comp_inv_smul_of_nonneg μ
      (fun w ↦ ((1 + ‖w‖) ^ (finrank ℝ E + 1))⁻¹) hR.le
    simp only [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hR, smul_eq_mul,
      inv_mul_eq_div] at h
    simp only [g, integral_const_mul, h]
    ring
  refine (lintegral_mono hf).trans_eq ?_
  rw [← hint, ← integral_sub_left_eq_self g μ x₀,
    ofReal_integral_eq_lintegral_ofReal (hg.comp_sub_left x₀) (ae_of_all _ fun w ↦ by positivity)]

end TauCeti
