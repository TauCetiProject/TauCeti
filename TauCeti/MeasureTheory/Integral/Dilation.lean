/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Analysis.Calculus.FDeriv.Comp

/-!
# Dilation scaling of the lower Lebesgue integral

Dilating the variable of a function on a finite-dimensional real normed space `E` by a nonzero
scalar `r` rescales its integral against an additive Haar measure by `|(r ^ n)⁻¹|`, where `n` is
the dimension of `E`. Mathlib records this for the Bochner integral as
`MeasureTheory.Measure.integral_comp_smul`; this file is the lower-Lebesgue-integral counterpart,
proved the same way from `MeasureTheory.Measure.map_addHaar_smul`, and, like the Bochner version,
needing no measurability hypothesis. Unlike the Bochner version, it needs `r ≠ 0`: for `r = 0`
the left-hand side is `g 0 * μ univ`, which is `∞` in positive dimension unless `g 0 = 0`.

## Main declarations

* `MeasureTheory.Measure.lintegral_comp_smul`:
  `∫⁻ x, g (r • x) ∂μ = |(r ^ n)⁻¹| * ∫⁻ x, g x ∂μ`.
* `MeasureTheory.Measure.lintegral_comp_inv_smul`: the same law written for `r⁻¹`, with factor
  `|r ^ n|`.
* `MeasureTheory.Measure.lintegral_comp_homothety`: the same law for the homothety of ratio `r`
  about any centre.
-/

public section

namespace MeasureTheory.Measure

open Module
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- **Dilation scaling of the lower Lebesgue integral.** This is the counterpart, for `∫⁻`, of
`MeasureTheory.Measure.integral_comp_smul`; as there, `g` need not be measurable. -/
theorem lintegral_comp_smul (g : E → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ x, g (r • x) ∂μ = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ x, g x ∂μ := by
  rw [← (measurableEmbedding_const_smul₀ hr).lintegral_map, map_addHaar_smul μ hr,
    lintegral_smul_measure, smul_eq_mul]

/-- Dilating the variable by `r⁻¹`, for `r ≠ 0`, multiplies a lower Lebesgue integral by
`|r ^ n|`, where `n` is the dimension of the ambient space. -/
theorem lintegral_comp_inv_smul (g : E → ℝ≥0∞) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ x, g (r⁻¹ • x) ∂μ = ENNReal.ofReal |r ^ finrank ℝ E| * ∫⁻ x, g x ∂μ := by
  rw [lintegral_comp_smul μ g (inv_ne_zero hr), inv_pow, inv_inv]

/-- **Homothety scaling of the lower Lebesgue integral.** Precomposing with the homothety of
ratio `r ≠ 0` about any centre `x` rescales a lower Lebesgue integral against an additive Haar
measure by `|(r ^ n)⁻¹|`, where `n` is the dimension of the ambient space. -/
theorem lintegral_comp_homothety (g : E → ℝ≥0∞) (x : E) {r : ℝ} (hr : r ≠ 0) :
    ∫⁻ y, g (AffineMap.homothety x r y) ∂μ =
      ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ y, g y ∂μ := by
  simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add]
  rw [lintegral_sub_right_eq_self (fun z => g (r • z + x)) x,
    lintegral_comp_smul μ (fun z => g (z + x)) hr, lintegral_add_right_eq_self]

end MeasureTheory.Measure

namespace TauCeti

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E]

/-- Dilation of the measure by a nonzero scalar rescales the squared derivative energy by the
inverse square of that scalar. -/
theorem integral_sq_norm_fderiv_comp_smul {μ : Measure E} {f : E → ℝ} {a : ℝ} (ha : a ≠ 0) :
    ∫ x, ‖fderiv ℝ f x‖ ^ 2 ∂μ.map (fun x ↦ a • x) =
      (a ^ 2)⁻¹ * ∫ x, ‖fderiv ℝ (fun y ↦ f (a • y)) x‖ ^ 2 ∂μ := by
  rw [(measurableEmbedding_const_smul₀ (α := E) ha).integral_map, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [norm_fderiv_comp_smul a, mul_pow, sq_abs]
  field_simp

end TauCeti
