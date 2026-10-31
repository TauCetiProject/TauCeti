/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import TauCeti.MeasureTheory.Function.Coarea.Eilenberg

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

Slicing by spheres is compatible with null sets: a Lebesgue-null set meets almost every sphere in
a Hausdorff-null set, so a.e. equal sets have the same spherical slices for almost every radius.
For a Lebesgue-measurable set `s` the volume `m(r) = volume (s ∩ ball c r)` is therefore the
integral of the slice measures `μHE[n - 1] (s ∩ sphere c ρ)` over `ρ ∈ (0, r)`, and by Lebesgue's
differentiation theorem on the line

`m'(r) = μHE[n - 1] (s ∩ sphere c r)` for almost every `r`.

More generally, the integral of a locally integrable function over `ball c r` has derivative its
integral over `sphere c r` at almost every radius. This identifies the growth rate of the volume in
balls appearing in density estimates for sets of finite perimeter with a boundary measure.

The inputs are the polar decomposition of volume, Mathlib's
`MeasureTheory.Measure.measurePreserving_homeomorphUnitSphereProd` and its integral forms such
as `TauCeti.lintegral_eq_lintegral_toSphere_lintegral_Ioi`, the identification of its surface
measure with Hausdorff measure, `TauCeti.euclideanHausdorffMeasure_restrict_sphere`, and
the rescaling of Hausdorff measure on spheres,
`TauCeti.euclideanHausdorffMeasure_restrict_sphere_eq_smul_map`. Null spherical slices come from
Eilenberg's inequality for the distance to the centre,
`LipschitzOnWith.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero`, and the radial derivatives
from Mathlib's Lebesgue differentiation theorem on the line,
`LocallyIntegrable.ae_hasDerivAt_integral`.

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

/-- **Null sets meet almost every sphere in a null set.** If `N` is Lebesgue-null, then for almost
every radius `r` the slice `N ∩ sphere c r` is null for `(n - 1)`-dimensional Hausdorff measure.
No measurability of `N` is needed. -/
theorem ae_euclideanHausdorffMeasure_inter_sphere_eq_zero (c : E) {N : Set E}
    (hN : volume N = 0) : ∀ᵐ r : ℝ, μHE[finrank ℝ E - 1] (N ∩ sphere c r) = 0 := by
  have hne : ∀ᵐ r : ℝ, r ≠ 0 := by simp [ae_iff, measure_singleton]
  rcases subsingleton_or_nontrivial E with hE | hE
  · filter_upwards [hne] with r hr
    rw [sphere_eq_empty_of_subsingleton hr, inter_empty, measure_empty]
  -- Spheres about `c` are the fibers of the `1`-Lipschitz map `x ↦ dist x c`, so Eilenberg's
  -- inequality shows that almost every fiber of a null set is null.
  have hN' : μHE[finrank ℝ ℝ + (finrank ℝ E - 1)] N = 0 := by
    rwa [finrank_self, add_comm, Nat.sub_add_cancel finrank_pos,
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume]
  have hfib (r : ℝ) : N ∩ (fun x ↦ dist x c) ⁻¹' {r} = N ∩ sphere c r := by
    ext x
    simp [dist_eq_norm]
  simpa only [hfib] using
    (LipschitzWith.dist_left c).lipschitzOnWith.ae_euclideanHausdorffMeasure_inter_preimage_eq_zero
      volume hN'

/-- Lebesgue-a.e. equal sets have, for almost every radius `r`, the same
`(n - 1)`-dimensional Hausdorff measure on the sphere `sphere c r`. No measurability of the sets
is needed. -/
theorem ae_euclideanHausdorffMeasure_inter_sphere_eq_of_ae_eq (c : E) {s t : Set E}
    (hst : s =ᵐ[volume] t) :
    ∀ᵐ r : ℝ, μHE[finrank ℝ E - 1] (s ∩ sphere c r) = μHE[finrank ℝ E - 1] (t ∩ sphere c r) := by
  obtain ⟨hst', hts'⟩ := ae_eq_set.1 hst
  filter_upwards [ae_euclideanHausdorffMeasure_inter_sphere_eq_zero c hst',
    ae_euclideanHausdorffMeasure_inter_sphere_eq_zero c hts'] with r h₁ h₂
  refine measure_congr (ae_eq_set.2 ⟨measure_mono_null (fun x hx ↦ ?_) h₁,
    measure_mono_null (fun x hx ↦ ?_) h₂⟩) <;>
  exact ⟨⟨hx.1.1, fun h ↦ hx.2 ⟨h, hx.1.2⟩⟩, hx.1.2⟩

/-- **Volume in a ball by spherical slices.** In a nontrivial real inner product space of
dimension `n`, the volume of a Lebesgue-measurable set `s` in the ball `ball c R` is the integral
over the radii `r ∈ (0, R)` of the `(n - 1)`-dimensional Hausdorff measures of its slices
`s ∩ sphere c r`. -/
theorem volume_inter_ball_eq_lintegral_Ioo_euclideanHausdorffMeasure_inter_sphere
    [Nontrivial E] (c : E) (R : ℝ) {s : Set E} (hs : NullMeasurableSet s volume) :
    volume (s ∩ ball c R) = ∫⁻ r in Ioo 0 R, μHE[finrank ℝ E - 1] (s ∩ sphere c r) := by
  set t := toMeasurable volume s
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have hst : s =ᵐ[volume] t := hs.toMeasurable_ae_eq.symm
  have h := setLIntegral_ball_eq_lintegral_Ioo_setLIntegral_sphere c R
    (measurable_one.indicator ht)
  simp_rw [lintegral_indicator_one ht, Measure.restrict_apply ht] at h
  rw [measure_congr (hst.inter (ae_eq_refl _)), h]
  exact lintegral_congr_ae (ae_restrict_of_ae
    ((ae_euclideanHausdorffMeasure_inter_sphere_eq_of_ae_eq c hst).mono fun r hr ↦ hr.symm))

/-- Below a fixed radius `R`, the ball integrals of a locally integrable function are primitives
of its sphere integrals, so Lebesgue's differentiation theorem on the line differentiates them. -/
private theorem ae_hasDerivAt_setIntegral_ball_of_lt [CompleteSpace F] [Nontrivial E] (c : E)
    {f : E → F} (hf : LocallyIntegrable f volume) (R : ℝ) :
    ∀ᵐ r : ℝ, r < R → HasDerivAt (fun ρ ↦ ∫ x in ball c ρ, f x)
      (∫ y in sphere c r, f y ∂μHE[finrank ℝ E - 1]) r := by
  have hfR : Integrable ((ball c R).indicator f) :=
    (integrable_indicator_iff measurableSet_ball).2
      ((hf.integrableOn_isCompact (isCompact_closedBall c R)).mono_set ball_subset_closedBall)
  -- The sphere integrals of `f` cut off outside `ball c R`, extended by zero to `r ≤ 0`.
  set G : ℝ → F := (Ioi 0).indicator fun r ↦
    ∫ y in sphere c r, (ball c R).indicator f y ∂μHE[finrank ℝ E - 1] with hGdef
  have hG : Integrable G :=
    (integrable_indicator_iff measurableSet_Ioi).2 (integrableOn_Ioi_setIntegral_sphere c hfR)
  have hcut (r : ℝ) (hr : r < R) :
      ∫ y in sphere c r, (ball c R).indicator f y ∂μHE[finrank ℝ E - 1] =
        ∫ y in sphere c r, f y ∂μHE[finrank ℝ E - 1] :=
    setIntegral_congr_fun isClosed_sphere.measurableSet fun y hy ↦
      indicator_of_mem (by rwa [mem_ball, mem_sphere.1 hy]) f
  -- Below `R`, the ball integrals of `f` are the primitive of `G` vanishing at zero.
  have hFG (ρ : ℝ) (hρ : ρ < R) : ∫ x in ball c ρ, f x = ∫ t in 0..ρ, G t := by
    rcases le_or_gt ρ 0 with h | h
    · rw [ball_eq_empty.2 h, Measure.restrict_empty, integral_zero_measure,
        intervalIntegral.integral_of_ge h, setIntegral_eq_zero_of_forall_eq_zero
          fun t (ht : t ∈ Ioc ρ 0) ↦ indicator_of_notMem (not_lt.2 ht.2) _, neg_zero]
    · rw [setIntegral_ball_eq_integral_Ioo_setIntegral_sphere c ρ
          ((hf.integrableOn_isCompact (isCompact_closedBall c ρ)).mono_set ball_subset_closedBall),
        intervalIntegral.integral_of_le h.le, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
      rw [hGdef, indicator_of_mem ht.1, hcut t (ht.2.trans hρ)]
  have hne : ∀ᵐ r : ℝ, r ≠ 0 := by simp [ae_iff, measure_singleton]
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hG.locallyIntegrable, hne]
    with r hr hr0 hrR
  have hd := (hr 0).congr_of_eventuallyEq ((eventually_lt_nhds hrR).mono fun ρ hρ ↦ hFG ρ hρ)
  convert hd using 1
  rcases hr0.lt_or_gt with h | h
  · rw [sphere_eq_empty_of_neg h, Measure.restrict_empty, integral_zero_measure, hGdef,
      indicator_of_notMem (not_lt.2 h.le)]
  · rw [hGdef, indicator_of_mem h, hcut r hrR]

/-- **Differentiating ball integrals in the radius.** For a locally integrable function `f`, at
almost every radius `r` the integral of `f` over the ball `ball c r` has derivative equal to the
integral of `f` against `(n - 1)`-dimensional Hausdorff measure on the sphere `sphere c r`. -/
theorem ae_hasDerivAt_setIntegral_ball [CompleteSpace F] (c : E) {f : E → F}
    (hf : LocallyIntegrable f volume) :
    ∀ᵐ r : ℝ, HasDerivAt (fun ρ ↦ ∫ x in ball c ρ, f x)
      (∫ y in sphere c r, f y ∂μHE[finrank ℝ E - 1]) r := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · -- In a trivial space spheres of nonzero radius are empty, and balls only depend on the sign
    -- of the radius.
    have hball (ρ : ℝ) : ball c ρ = {_x | 0 < ρ} := by
      ext x
      simp [Subsingleton.elim x c]
    have hne : ∀ᵐ r : ℝ, r ≠ 0 := by simp [ae_iff, measure_singleton]
    filter_upwards [hne] with r hr
    rw [sphere_eq_empty_of_subsingleton hr, Measure.restrict_empty, integral_zero_measure]
    refine (hasDerivAt_const r (∫ x in ball c r, f x)).congr_of_eventuallyEq ?_
    rcases hr.lt_or_gt with h | h
    · filter_upwards [eventually_lt_nhds h] with ρ hρ
      simp only [hball, not_lt.2 hρ.le, not_lt.2 h.le]
    · filter_upwards [eventually_gt_nhds h] with ρ hρ
      simp only [hball, hρ, h]
  -- Every radius lies below some natural number.
  filter_upwards [ae_all_iff.2 fun n : ℕ ↦ ae_hasDerivAt_setIntegral_ball_of_lt c hf n]
    with r hr
  obtain ⟨n, hn⟩ := exists_nat_gt r
  exact hr n hn

/-- **The radial derivative of the volume in balls.** For a Lebesgue-measurable set `s`, at almost
every radius `r` the volume `m(ρ) = volume (s ∩ ball c ρ)` has derivative
`m'(r) = μHE[n - 1] (s ∩ sphere c r)`, the `(n - 1)`-dimensional Hausdorff measure of the slice of
`s` by the sphere `sphere c r`. -/
theorem ae_hasDerivAt_measureReal_inter_ball (c : E) {s : Set E}
    (hs : NullMeasurableSet s volume) :
    ∀ᵐ r : ℝ, HasDerivAt (fun ρ ↦ volume.real (s ∩ ball c ρ))
      (μHE[finrank ℝ E - 1].real (s ∩ sphere c r)) r := by
  set t := toMeasurable volume s
  have ht : MeasurableSet t := measurableSet_toMeasurable _ _
  have hst : s =ᵐ[volume] t := hs.toMeasurable_ae_eq.symm
  have hm : (fun ρ ↦ volume.real (s ∩ ball c ρ)) = fun ρ ↦ ∫ x in ball c ρ, t.indicator 1 x := by
    funext ρ
    rw [integral_indicator_one ht, measureReal_restrict_apply ht,
      measureReal_congr (hst.inter (ae_eq_refl _))]
  filter_upwards [ae_hasDerivAt_setIntegral_ball (f := t.indicator 1) c
      ((locallyIntegrable_const (1 : ℝ)).indicator ht),
    ae_euclideanHausdorffMeasure_inter_sphere_eq_of_ae_eq c hst] with r hr hr'
  rw [hm, measureReal_def, hr', ← measureReal_def, ← measureReal_restrict_apply ht,
    ← integral_indicator_one ht]
  exact hr

end TauCeti
