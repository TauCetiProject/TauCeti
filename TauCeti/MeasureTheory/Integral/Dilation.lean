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

Dilating each coordinate of `ℝ^ι` by its own nonzero factor `cᵢ` rescales an additive Haar
measure by `|∏ᵢ cᵢ|⁻¹` (`MeasureTheory.Measure.map_mul_pi_addHaar_eq_smul`), by Mathlib's
`MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar` for the diagonal matrix of the
factors, and so rescales the Bochner integral by the same factor (`TauCeti.integral_comp_mul_pi`).

## Main declarations

* `MeasureTheory.Measure.lintegral_comp_smul`:
  `∫⁻ x, g (r • x) ∂μ = |(r ^ n)⁻¹| * ∫⁻ x, g x ∂μ`.
* `MeasureTheory.Measure.lintegral_comp_inv_smul`: the same law written for `r⁻¹`, with factor
  `|r ^ n|`.
* `MeasureTheory.Measure.lintegral_comp_homothety`: the same law for the homothety of ratio `r`
  about any centre.
* `MeasureTheory.Measure.map_mul_pi_addHaar_eq_smul`: the image of an additive Haar measure on
  `ℝ^ι` under `x ↦ (cᵢ xᵢ)ᵢ` is the measure scaled by `|∏ᵢ cᵢ|⁻¹`.
* `TauCeti.integral_comp_mul_pi`: `∫ x, F (fun i ↦ cᵢ xᵢ) = |∏ᵢ cᵢ|⁻¹ • ∫ y, F y` on `ℝ^ι`.
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

/-- **Rescaling the coordinates of `ℝ^ι`.** The image of an additive Haar measure under the
map multiplying the `i`-th coordinate by `cᵢ ≠ 0` is the measure scaled by `|∏ᵢ cᵢ|⁻¹`. -/
theorem map_mul_pi_addHaar_eq_smul {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ))
    [μ.IsAddHaarMeasure] {c : ι → ℝ} (hc : ∀ i, c i ≠ 0) :
    μ.map (fun x i ↦ c i * x i) = ENNReal.ofReal |∏ i, c i|⁻¹ • μ := by
  classical
  have he : (fun (x : ι → ℝ) i ↦ c i * x i) = Matrix.toLin' (Matrix.diagonal c) := by
    funext x i
    simp [Matrix.mulVec_diagonal]
  have hdet : LinearMap.det (Matrix.toLin' (Matrix.diagonal c)) = ∏ i, c i := by
    rw [LinearMap.det_toLin', Matrix.det_diagonal]
  rw [he, Measure.map_linearMap_addHaar_eq_smul_addHaar μ
    (hdet ▸ Finset.prod_ne_zero_iff.2 fun i _ ↦ hc i), hdet, abs_inv]

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

/-- Multiplying the `i`-th coordinate by `cᵢ ≠ 0` scales the integral against an additive Haar
measure on `ℝ^ι` by `|∏ᵢ cᵢ|⁻¹`. -/
theorem integral_comp_mul_pi {ι G : Type*} [Fintype ι] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {μ : Measure (ι → ℝ)} [μ.IsAddHaarMeasure] {c : ι → ℝ} (hc : ∀ i, c i ≠ 0)
    (F : (ι → ℝ) → G) :
    ∫ x, F (fun i ↦ c i * x i) ∂μ = |∏ i, c i|⁻¹ • ∫ y, F y ∂μ := by
  let e : (ι → ℝ) ≃ᵐ (ι → ℝ) :=
    (Homeomorph.piCongrRight fun i ↦ Homeomorph.mulLeft₀ (c i) (hc i)).toMeasurableEquiv
  have he : ⇑e = fun x i ↦ c i * x i := by
    funext x i
    simp [e]
  have h := integral_map_equiv (μ := μ) e F
  rw [he, Measure.map_mul_pi_addHaar_eq_smul μ hc,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity)] at h
  exact h.symm

end TauCeti
