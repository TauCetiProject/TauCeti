/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Analysis.Calculus.FDeriv.Comp
import TauCeti.MeasureTheory.Integral.Bochner.Affine

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
factors. The Bochner integral is rescaled by the same factor (`TauCeti.integral_comp_mul_pi`), by
the linear change of variables `MeasureTheory.Measure.integral_comp_continuousLinearEquiv` for the
diagonal automorphism.

## Main declarations

* `MeasureTheory.Measure.lintegral_comp_smul`:
  `∫⁻ x, g (r • x) ∂μ = |(r ^ n)⁻¹| * ∫⁻ x, g x ∂μ`.
* `MeasureTheory.Measure.lintegral_comp_inv_smul`: the same law written for `r⁻¹`, with factor
  `|r ^ n|`.
* `MeasureTheory.Measure.lintegral_comp_homothety`: the same law for the homothety of ratio `r`
  about any centre.
* `MeasureTheory.Measure.setLIntegral_comp_add_smul`: the same law for the affine map
  `y ↦ c + r • y`, on the preimage of any set.
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

/-- **Affine scaling of a set lower Lebesgue integral.** Precomposing with `y ↦ c + r • y`,
`r ≠ 0`, and integrating over the preimage of a set `s` gives `|(r ^ n)⁻¹|` times the integral over
`s`, where `n` is the dimension of the ambient space. Neither `g` nor `s` need be measurable. -/
theorem setLIntegral_comp_add_smul (g : E → ℝ≥0∞) (c : E) {r : ℝ} (hr : r ≠ 0) (s : Set E) :
    ∫⁻ y in (fun y ↦ c + r • y) ⁻¹' s, g (c + r • y) ∂μ =
      ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| * ∫⁻ z in s, g z ∂μ := by
  have he : MeasurableEmbedding fun y : E ↦ c + r • y :=
    (measurableEmbedding_addLeft c).comp (measurableEmbedding_const_smul₀ hr)
  have hmap : μ.map (fun y ↦ c + r • y) = ENNReal.ofReal |(r ^ finrank ℝ E)⁻¹| • μ := by
    calc μ.map (fun y ↦ c + r • y) = (μ.map (r • ·)).map (c + ·) :=
          (Measure.map_map (measurable_const_add c) (measurable_const_smul r)).symm
      _ = _ := by
          rw [map_addHaar_smul μ hr, Measure.map_smul _ (measurable_const_add c).aemeasurable,
            map_add_left_eq_self]
  rw [← he.lintegral_map, ← he.restrict_map, hmap, Measure.restrict_smul, lintegral_smul_measure,
    smul_eq_mul]

/-- Multiplying the `i`-th coordinate of `ℝ^ι` by `cᵢ` is the linear map of the diagonal matrix
of the `cᵢ`. -/
private theorem mul_pi_eq_toLin'_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    (fun (x : ι → ℝ) i ↦ c i * x i) = Matrix.toLin' (Matrix.diagonal c) := by
  funext x i
  simp [Matrix.mulVec_diagonal]

/-- The determinant of multiplying the `i`-th coordinate of `ℝ^ι` by `cᵢ` is `∏ᵢ cᵢ`. -/
private theorem det_toLin'_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℝ) :
    LinearMap.det (Matrix.toLin' (Matrix.diagonal c)) = ∏ i, c i := by
  rw [LinearMap.det_toLin', Matrix.det_diagonal]

/-- **Rescaling the coordinates of `ℝ^ι`.** The image of an additive Haar measure under the
map multiplying the `i`-th coordinate by `cᵢ ≠ 0` is the measure scaled by `|∏ᵢ cᵢ|⁻¹`. -/
theorem map_mul_pi_addHaar_eq_smul {ι : Type*} [Fintype ι] (μ : Measure (ι → ℝ))
    [μ.IsAddHaarMeasure] {c : ι → ℝ} (hc : ∀ i, c i ≠ 0) :
    μ.map (fun x i ↦ c i * x i) = ENNReal.ofReal |∏ i, c i|⁻¹ • μ := by
  classical
  rw [mul_pi_eq_toLin'_diagonal, Measure.map_linearMap_addHaar_eq_smul_addHaar μ
    (det_toLin'_diagonal c ▸ Finset.prod_ne_zero_iff.2 fun i _ ↦ hc i), det_toLin'_diagonal,
    abs_inv]

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
  classical
  -- The coordinatewise dilation is the automorphism given by the diagonal matrix of the `cᵢ`.
  let e : (ι → ℝ) ≃L[ℝ] (ι → ℝ) :=
    (LinearMap.equivOfDetNeZero _ (Measure.det_toLin'_diagonal c ▸
      Finset.prod_ne_zero_iff.2 fun i _ ↦ hc i)).toContinuousLinearEquiv
  have hlin : (e : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) = Matrix.toLin' (Matrix.diagonal c) := by
    rw [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, LinearEquiv.coe_ofIsUnitDet]
  have he : ⇑e = fun x i ↦ c i * x i := by
    rw [Measure.mul_pi_eq_toLin'_diagonal, ← hlin, LinearEquiv.coe_coe,
      ContinuousLinearEquiv.coe_toLinearEquiv]
  have h := Measure.integral_comp_continuousLinearEquiv μ F e
  rwa [he, hlin, Measure.det_toLin'_diagonal] at h

end TauCeti
