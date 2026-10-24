/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.MeasureTheory.Constructions.HaarToSphere

/-!
# Polar integration against Hausdorff measure on spheres

Let `E` be a nontrivial real inner product space of dimension `n`. This file proves the polar
integration formula with respect to the normalized `(n - 1)`-dimensional Hausdorff measure
`μHE[n - 1]` on spheres:

`∫ x, f x = ∫ r in (0, ∞), ∫ y in sphere c r, f y ∂μHE[n - 1]`.

No radial Jacobian appears: the factor `r ^ (n - 1)` of polar coordinates is absorbed into the
Hausdorff measure of the sphere of radius `r`. The nonnegative version holds for every measurable
function and allows infinite integrals. For an integrable function, almost every sphere carries an
integrable restriction, the sphere integrals are integrable in the radius, and the Bochner formula
holds. The ball versions integrate over the radii `r ∈ (0, R)`.

The inputs are the polar decomposition of volume, Mathlib's
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` and its integral forms such
as `TauCeti.lintegral_eq_lintegral_toSphere_lintegral_Ioi`, the identification of its surface
measure with Hausdorff measure, `TauCeti.euclideanHausdorffMeasure_restrict_sphere`, and
the rescaling of Hausdorff measure on spheres,
`TauCeti.euclideanHausdorffMeasure_restrict_sphere_eq_smul_map`.

## Main results

* `TauCeti.lintegral_eq_lintegral_Ioi_setLIntegral_sphere`,
  `TauCeti.setLIntegral_ball_eq_lintegral_Ioo_setLIntegral_sphere`: nonnegative polar integration
  over the whole space and over balls.
* `TauCeti.ae_integrableOn_sphere`, `TauCeti.integrableOn_Ioi_setIntegral_sphere`: integrability on
  almost every sphere and of the sphere integrals.
* `TauCeti.integral_eq_integral_Ioi_setIntegral_sphere`,
  `TauCeti.setIntegral_ball_eq_integral_Ioo_setIntegral_sphere`: Bochner polar integration over
  the whole space and over balls.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.4 (the coarea formula and integration in polar coordinates).
-/

public section

noncomputable section

open MeasureTheory Measure Module Set Metric
open scoped Pointwise ENNReal

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Integration against Mathlib's surface measure on the unit sphere, transported to the sphere
`sphere c r` by `u ↦ c + r • u`, is integration against Hausdorff measure on `sphere c r`. -/
private lemma setLIntegral_sphere_eq_mul_lintegral_toSphere (c : E) {r : ℝ} (hr : 0 < r)
    (f : E → ℝ≥0∞) :
    ∫⁻ y in sphere c r, f y ∂μHE[finrank ℝ E - 1] =
      ENNReal.ofReal (r ^ (finrank ℝ E - 1)) *
        ∫⁻ u : sphere (0 : E) 1, f (c + r • (u : E)) ∂(volume : Measure E).toSphere := by
  rw [setLIntegral_sphere_eq_mul_setLIntegral_sphere_zero_one _ c hr,
    euclideanHausdorffMeasure_restrict_sphere,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).lintegral_map,
    ENNReal.ofReal_pow hr.le]

/-- Integration against Mathlib's surface measure on the unit sphere, transported to the sphere
`sphere c r` by `u ↦ c + r • u`, is integration against Hausdorff measure on `sphere c r`. -/
private lemma setIntegral_sphere_eq_smul_integral_toSphere (c : E) {r : ℝ} (hr : 0 < r)
    (f : E → F) :
    ∫ y in sphere c r, f y ∂μHE[finrank ℝ E - 1] = r ^ (finrank ℝ E - 1) •
      ∫ u : sphere (0 : E) 1, f (c + r • (u : E)) ∂(volume : Measure E).toSphere := by
  rw [setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one _ c hr,
    euclideanHausdorffMeasure_restrict_sphere,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).integral_map]

/-- **Integration in polar coordinates against Hausdorff measure.** In a nontrivial real inner
product space of dimension `n`, the integral of a measurable nonnegative function is the integral
over the radii `r ∈ (0, ∞)` of its integrals against `(n - 1)`-dimensional Hausdorff measure on
the spheres `sphere c r`. -/
theorem lintegral_eq_lintegral_Ioi_setLIntegral_sphere [Nontrivial E] (c : E)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ y in sphere c r, f y ∂μHE[finrank ℝ E - 1] := by
  have hfc : Measurable fun x ↦ f (c + x) := hf.comp (measurable_const_add c)
  -- Translate to the origin, pass to polar coordinates, and swap the two integrals.
  rw [← lintegral_add_left_eq_self f c, lintegral_eq_lintegral_toSphere_lintegral_Ioi hfc,
    lintegral_lintegral_swap (by fun_prop)]
  refine setLIntegral_congr_fun measurableSet_Ioi fun r hr ↦ ?_
  rw [setLIntegral_sphere_eq_mul_lintegral_toSphere c hr f,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- **Integration over a ball in polar coordinates against Hausdorff measure.** In a nontrivial
real inner product space of dimension `n`, the integral of a measurable nonnegative function over
the ball `ball c R` is the integral over the radii `r ∈ (0, R)` of its integrals against
`(n - 1)`-dimensional Hausdorff measure on the spheres `sphere c r`. -/
theorem setLIntegral_ball_eq_lintegral_Ioo_setLIntegral_sphere [Nontrivial E] (c : E) (R : ℝ)
    {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in ball c R, f x =
      ∫⁻ r in Ioo 0 R, ∫⁻ y in sphere c r, f y ∂μHE[finrank ℝ E - 1] := by
  rw [← lintegral_indicator measurableSet_ball,
    lintegral_eq_lintegral_Ioi_setLIntegral_sphere c (hf.indicator measurableSet_ball),
    ← Ioi_inter_Iio, inter_comm (Ioi _), ← restrict_restrict measurableSet_Iio,
    ← lintegral_indicator measurableSet_Iio]
  -- On the sphere of radius `r`, the truncation agrees with `f` if `r < R` and vanishes otherwise.
  refine setLIntegral_congr_fun measurableSet_Ioi fun r _ ↦ ?_
  by_cases hrR : r < R
  · rw [indicator_of_mem (mem_Iio.2 hrR)]
    refine setLIntegral_congr_fun isClosed_sphere.measurableSet fun y hy ↦ indicator_of_mem ?_ f
    rwa [mem_ball, mem_sphere.1 hy]
  · rw [indicator_of_notMem (by simpa using hrR)]
    refine (setLIntegral_congr_fun isClosed_sphere.measurableSet
      fun y hy ↦ indicator_of_notMem ?_ f).trans lintegral_zero
    rwa [mem_ball, mem_sphere.1 hy]

/-- An integrable function is integrable against `(n - 1)`-dimensional Hausdorff measure on the
sphere `sphere c r` for almost every radius `r > 0`. -/
theorem ae_integrableOn_sphere (c : E) {f : E → F} (hf : Integrable f) :
    ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))),
      IntegrableOn f (sphere c r) μHE[finrank ℝ E - 1] := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [sphere_eq_empty_of_subsingleton (ne_of_gt hr)]
    exact integrableOn_empty
  have hint := (integrable_and_integral_eq_integral_prod_toSphere (μ := volume)
    (fun x ↦ f (c + (x : E))) (hf.comp_add_left c)).1
  -- Almost every radius for the radial measure, which has a positive density on `(0, ∞)`.
  have hae : ∀ᵐ r : Ioi (0 : ℝ) ∂(volume.comap ((↑) : Ioi (0 : ℝ) → ℝ)),
      Integrable (fun u : sphere (0 : E) 1 ↦ f (c + (r : ℝ) • (u : E)))
        (volume : Measure E).toSphere :=
    withDensity_absolutelyContinuous'
      (measurable_subtype_coe.pow_const _).ennreal_ofReal.aemeasurable
      (ae_of_all _ fun r ↦ (ENNReal.ofReal_pos.2 (pow_pos r.2 _)).ne') hint.prod_left_ae
  rw [ae_restrict_iff_subtype measurableSet_Ioi]
  filter_upwards [hae] with r hr
  rw [integrableOn_sphere_iff _ c r.2, IntegrableOn, euclideanHausdorffMeasure_restrict_sphere,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).integrable_map_iff]
  exact hr

/-- For an integrable function, the integrals against `(n - 1)`-dimensional Hausdorff measure on
the spheres `sphere c r` are integrable in the radius `r ∈ (0, ∞)`. -/
theorem integrableOn_Ioi_setIntegral_sphere (c : E) {f : E → F} (hf : Integrable f) :
    IntegrableOn (fun r ↦ ∫ y in sphere c r, f y ∂μHE[finrank ℝ E - 1]) (Ioi 0) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · refine integrableOn_zero.congr_fun (fun r hr ↦ ?_) measurableSet_Ioi
    rw [sphere_eq_empty_of_subsingleton (ne_of_gt hr), restrict_empty, integral_zero_measure]
  have hint := (integrable_and_integral_eq_integral_prod_toSphere (μ := volume)
    (fun x ↦ f (c + (x : E))) (hf.comp_add_left c)).1.integral_prod_right
  rw [volumeIoiPow, integrable_withDensity_iff_integrable_smul'
      (measurable_subtype_coe.pow_const _).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)] at hint
  rw [integrableOn_iff_comap_subtypeVal measurableSet_Ioi]
  refine hint.congr (ae_of_all _ fun r ↦ ?_)
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) _)]
  exact (setIntegral_sphere_eq_smul_integral_toSphere c r.2 f).symm

/-- **Integration in polar coordinates against Hausdorff measure.** In a nontrivial real inner
product space of dimension `n`, the integral of an integrable function is the integral over the
radii `r ∈ (0, ∞)` of its integrals against `(n - 1)`-dimensional Hausdorff measure on the
spheres `sphere c r`. -/
theorem integral_eq_integral_Ioi_setIntegral_sphere [Nontrivial E] (c : E) {f : E → F}
    (hf : Integrable f) :
    ∫ x, f x = ∫ r in Ioi (0 : ℝ), ∫ y in sphere c r, f y ∂μHE[finrank ℝ E - 1] := by
  rw [← integral_add_left_eq_self f c,
    integral_eq_integral_Ioi_integral_toSphere _ (hf.comp_add_left c)]
  exact setIntegral_congr_fun measurableSet_Ioi fun r hr ↦
    (setIntegral_sphere_eq_smul_integral_toSphere c hr f).symm

/-- **Integration over a ball in polar coordinates against Hausdorff measure.** In a nontrivial
real inner product space of dimension `n`, the integral over the ball `ball c R` of a function
integrable there is the integral over the radii `r ∈ (0, R)` of its integrals against
`(n - 1)`-dimensional Hausdorff measure on the spheres `sphere c r`. -/
theorem setIntegral_ball_eq_integral_Ioo_setIntegral_sphere [Nontrivial E] (c : E) (R : ℝ)
    {f : E → F} (hf : IntegrableOn f (ball c R)) :
    ∫ x in ball c R, f x =
      ∫ r in Ioo 0 R, ∫ y in sphere c r, f y ∂μHE[finrank ℝ E - 1] := by
  -- Translate the ball to the origin and use polar integration over balls about the origin.
  have hmp := measurePreserving_add_left (volume : Measure E) c
  have hpre : (c + ·) ⁻¹' ball c R = ball 0 R := by rw [preimage_add_ball, sub_self]
  rw [← hmp.setIntegral_preimage_emb (measurableEmbedding_addLeft c), hpre,
    setIntegral_ball_zero_eq_integral_Ioo
      (hpre ▸ (hmp.integrableOn_comp_preimage (measurableEmbedding_addLeft c)).2 hf)]
  exact setIntegral_congr_fun measurableSet_Ioo fun r hr ↦
    (setIntegral_sphere_eq_smul_integral_toSphere c hr.1 f).symm

end TauCeti
