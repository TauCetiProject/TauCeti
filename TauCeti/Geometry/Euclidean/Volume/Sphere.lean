/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.MeasureTheory.Function.AreaFormula.Basic

import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.Calculus.FDeriv.Norm
import TauCeti.Analysis.InnerProductSpace.NormDet
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# Hausdorff measure of spheres

Let `E` be a real inner product space of dimension `n`. Mathlib's surface measure
`Measure.toSphere volume` on the unit sphere is defined through cones: a set `s` of the sphere
has measure `n` times the volume of `Ioo 0 1 • s`. This file identifies it with the normalized
`(n - 1)`-dimensional Hausdorff measure `μHE[n - 1]` of the sphere, and deduces

`μHE[n - 1] (sphere c r) = n ω_n r ^ (n - 1)`, for `r > 0`,

where `ω_n = volume (ball 0 1)`. These are the constants of polar integration with respect to
Hausdorff measure, and they agree with Mathlib's volume of balls. The passage from the unit sphere
to `sphere c r` is a rescaling statement valid for every dimension `d` in every real normed space:
`μHE[d]` on `sphere c r` is `r ^ d` times the pushforward of `μHE[d]` on the unit sphere by
`u ↦ c + r • u`.

The comparison is a cone formula for parametrizations of pieces of the unit sphere. If
`ψ : W → E` takes values in the unit sphere near a measurable set `s`, where `dim W = n - 1`, and
`ψ` is injective on `s` with injective derivative, then `(t, w) ↦ t • ψ w` parametrizes the cone
`Ioo 0 1 • ψ '' s`. Since `ψ w` is a unit vector orthogonal to the range of the derivative of `ψ`,
the Jacobian of the cone map at `(t, w)` is `t ^ (n - 1)` times the Jacobian of `ψ` at `w`
(`LinearMap.normDet_toSpanSingleton_coprod`). The area formula applied to both maps, and
integration of `t ^ (n - 1)` over `(0, 1)`, give
`μHE[n - 1] (ψ '' s) = n volume (Ioo 0 1 • ψ '' s)`.
The inverse of Mathlib's stereographic projection from a unit vector `v` parametrizes the sphere
minus `v` in this way, and the projections from `v` and `-v` together cover the sphere. No
lower bound on the dimension is needed: in dimension one, both measures count points.

## Main results

* `TauCeti.euclideanHausdorffMeasure_restrict_sphere_eq_smul_map`: rescaling Hausdorff measure on
  spheres, with the integral and integrability forms
  `TauCeti.setLIntegral_sphere_eq_mul_setLIntegral_sphere_zero_one`,
  `TauCeti.setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one` and
  `TauCeti.integrableOn_sphere_iff`.
* `TauCeti.euclideanHausdorffMeasure_image_eq_finrank_mul_volume_Ioo_smul`: the cone formula for
  a regular injective parametrization of a piece of the unit sphere.
* `TauCeti.toSphere_volume_eq_comap_euclideanHausdorffMeasure`: Mathlib's surface measure on the
  unit sphere is normalized `(n - 1)`-dimensional Hausdorff measure.
* `TauCeti.euclideanHausdorffMeasure_restrict_sphere`: the same comparison as measures on `E`.
* `TauCeti.euclideanHausdorffMeasure_sphere_zero_one_eq_ofReal`: the unit sphere has
  `(n - 1)`-dimensional Hausdorff measure `2 π ^ (n / 2) / Γ(n / 2)`.
* `TauCeti.toSphere_volume_apply_univ`: the same value `2 π ^ (n / 2) / Γ(n / 2)` for the total
  mass of Mathlib's surface measure `Measure.toSphere volume`.
* `TauCeti.euclideanHausdorffMeasure_sphere`: `μHE[n - 1] (sphere c r) = n ω_n r ^ (n - 1)`.
* `TauCeti.roundSphereVolume`: the area `|Sⁿ|` of the unit round sphere `Sⁿ ⊆ ℝⁿ⁺¹`, its normalized
  `n`-dimensional Hausdorff measure (not the ambient Lebesgue measure, which vanishes).
* `TauCeti.euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume`: the unit sphere of every
  real inner product space of dimension `n + 1` has `n`-dimensional Hausdorff measure `|Sⁿ|`; in
  particular this measure is finite.
* `TauCeti.roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma`, `TauCeti.roundSphereVolume_pos`: the
  value `|Sⁿ| = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)` and the positivity of `|Sⁿ|`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §3.3 (the area formula).
-/

public section

noncomputable section

open MeasureTheory Measure Module Set Filter Function Metric
open scoped Pointwise ENNReal Topology RealInnerProductSpace

namespace TauCeti

section Scaling

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F]

/-- The affine map `u ↦ c + r • u`, as a measurable equivalence. -/
private def addSMulEquiv (c : E) {r : ℝ} (hr : r ≠ 0) : E ≃ᵐ E :=
  ((Homeomorph.smulOfNeZero r hr).trans (Homeomorph.addLeft c)).toMeasurableEquiv

private lemma addSMulEquiv_apply (c : E) {r : ℝ} (hr : r ≠ 0) (u : E) :
    addSMulEquiv c hr u = c + r • u := rfl

/-- **Rescaling Hausdorff measure on spheres.** For `r > 0`, the `d`-dimensional Hausdorff measure
on the sphere `sphere c r` is `r ^ d` times the pushforward of the `d`-dimensional Hausdorff
measure on the unit sphere by `u ↦ c + r • u`. -/
theorem euclideanHausdorffMeasure_restrict_sphere_eq_smul_map (d : ℕ) (c : E) {r : ℝ}
    (hr : 0 < r) :
    (μHE[d] : Measure E).restrict (sphere c r) = ENNReal.ofReal r ^ d •
      ((μHE[d] : Measure E).restrict (sphere 0 1)).map (fun u ↦ c + r • u) := by
  set φ := addSMulEquiv c hr.ne'
  have hφ : ⇑φ = fun u ↦ c + r • u := funext (addSMulEquiv_apply c hr.ne')
  have hpre : φ ⁻¹' sphere c r = sphere 0 1 := by
    ext u
    simp only [mem_preimage, hφ, mem_sphere_iff_norm, add_sub_cancel_left, norm_smul,
      Real.norm_of_nonneg hr.le, sub_zero]
    exact ⟨fun h ↦ (mul_eq_left₀ hr.ne').1 h, fun h ↦ by rw [h, mul_one]⟩
  -- Hausdorff measure of an image under `φ`: translation is an isometry, and dilation by `r`
  -- multiplies the measure by `r ^ d`.
  have himage (s : Set E) : μHE[d] (φ '' s) = ENNReal.ofReal r ^ d * μHE[d] s := by
    have : φ '' s = (c + ·) '' (r • s) := by
      rw [hφ, ← image_smul, image_image]
    rw [this, (isometry_add_left c).euclideanHausdorffMeasure_image,
      euclideanHausdorffMeasure_smul₀ _ hr.ne']
    simp [ENNReal.smul_def, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hr.le]
  rw [← hφ]
  ext s hs
  rw [restrict_apply hs, Measure.smul_apply, φ.map_apply,
    restrict_apply' isClosed_sphere.measurableSet, ← hpre, ← preimage_inter, smul_eq_mul, ← himage,
    φ.image_preimage]

/-- **Rescaling integrals over spheres.** For `r > 0`, integrating a nonnegative function against
`d`-dimensional Hausdorff measure on `sphere c r` amounts to integrating its pullback by
`u ↦ c + r • u` over the unit sphere, with the factor `r ^ d`. -/
theorem setLIntegral_sphere_eq_mul_setLIntegral_sphere_zero_one (d : ℕ) (c : E) {r : ℝ}
    (hr : 0 < r) (f : E → ℝ≥0∞) :
    ∫⁻ y in sphere c r, f y ∂μHE[d] =
      ENNReal.ofReal r ^ d * ∫⁻ u in sphere 0 1, f (c + r • u) ∂μHE[d] := by
  rw [euclideanHausdorffMeasure_restrict_sphere_eq_smul_map d c hr, lintegral_smul_measure,
    ← funext (addSMulEquiv_apply c hr.ne'), lintegral_map_equiv, smul_eq_mul]
  simp only [addSMulEquiv_apply]

/-- **Rescaling integrals over spheres.** For `r > 0`, integrating a function against
`d`-dimensional Hausdorff measure on `sphere c r` amounts to integrating its pullback by
`u ↦ c + r • u` over the unit sphere, with the factor `r ^ d`. -/
theorem setIntegral_sphere_eq_smul_setIntegral_sphere_zero_one [NormedSpace ℝ F] (d : ℕ)
    (c : E) {r : ℝ} (hr : 0 < r) (f : E → F) :
    ∫ y in sphere c r, f y ∂μHE[d] = r ^ d • ∫ u in sphere 0 1, f (c + r • u) ∂μHE[d] := by
  rw [euclideanHausdorffMeasure_restrict_sphere_eq_smul_map d c hr, integral_smul_measure,
    ← funext (addSMulEquiv_apply c hr.ne'),
    (addSMulEquiv c hr.ne').measurableEmbedding.integral_map, ← ENNReal.ofReal_pow hr.le,
    ENNReal.toReal_ofReal (pow_nonneg hr.le d)]
  simp only [addSMulEquiv_apply]

/-- A function is integrable for `d`-dimensional Hausdorff measure on `sphere c r`, `r > 0`, if
and only if its pullback by `u ↦ c + r • u` is integrable on the unit sphere. -/
theorem integrableOn_sphere_iff (d : ℕ) (c : E) {r : ℝ} (hr : 0 < r) {f : E → F} :
    IntegrableOn f (sphere c r) μHE[d] ↔
      IntegrableOn (fun u ↦ f (c + r • u)) (sphere 0 1) μHE[d] := by
  rw [IntegrableOn, euclideanHausdorffMeasure_restrict_sphere_eq_smul_map d c hr,
    integrable_smul_measure (pow_ne_zero _ (ENNReal.ofReal_pos.2 hr).ne')
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
    ← funext (addSMulEquiv_apply c hr.ne'),
    (addSMulEquiv c hr.ne').measurableEmbedding.integrable_map_iff]
  simp only [IntegrableOn, Function.comp_def, addSMulEquiv_apply]

end Scaling

variable {W E : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Cone formula.** Let `ψ : W → E` take values in the unit sphere near a measurable set `s`,
where `dim W + 1 = dim E`, and let `ψ` be injective on `s` and differentiable on `s` with injective
derivative. Then the `dim W`-dimensional Hausdorff measure of `ψ '' s` is `dim E` times the
volume of the cone `Ioo 0 1 • ψ '' s`. -/
theorem euclideanHausdorffMeasure_image_eq_finrank_mul_volume_Ioo_smul {ψ : W → E} {s : Set W}
    (hdim : finrank ℝ W + 1 = finrank ℝ E) (hs : MeasurableSet s)
    (hψ : ∀ w ∈ s, ∀ᶠ y in 𝓝 w, ‖ψ y‖ = 1) (hd : ∀ w ∈ s, DifferentiableAt ℝ ψ w)
    (hinj : ∀ w ∈ s, Injective (fderiv ℝ ψ w)) (hψs : InjOn ψ s) :
    μHE[finrank ℝ W] (ψ '' s) = finrank ℝ E * volume (Ioo (0 : ℝ) 1 • (ψ '' s)) := by
  -- We apply the area formula to the cone map `Φ (t, w) = t • ψ w` on `Ioo 0 1 × s`, which is
  -- injective with image the cone and has Jacobian `t ^ k` times that of `ψ`. Fubini–Tonelli then
  -- separates `∫ t ^ k = 1 / (k + 1)` from `∫ J ψ`, which is `μHE[k] (ψ '' s)` by the area formula.
  set k := finrank ℝ W
  have hnorm : ∀ w ∈ s, ‖ψ w‖ = 1 := fun w hw => (hψ w hw).self_of_nhds
  have horth : ∀ w ∈ s, ∀ u, ⟪ψ w, fderiv ℝ ψ w u⟫ = 0 := fun w hw =>
    inner_fderiv_eq_zero_of_eventually_norm_eq ((hψ w hw).mono fun y hy => by rw [hy, hnorm w hw])
  -- The cone map `(t, w) ↦ t • ψ w` on the Euclidean product `ℝ × W`.
  let Φ : WithLp 2 (ℝ × W) → E := fun x => (WithLp.ofLp x).1 • ψ (WithLp.ofLp x).2
  let S : Set (WithLp 2 (ℝ × W)) := WithLp.ofLp ⁻¹' (Ioo 0 1 ×ˢ s)
  have hS : MeasurableSet S :=
    (measurableSet_Ioo.prod hs).preimage (WithLp.prod_continuous_ofLp 2 ℝ W).measurable
  -- Its derivative at `(t, w)` sends `(a, u)` to `a • ψ w + t • ψ' w u`.
  have hΦ : ∀ x ∈ S, HasFDerivAt Φ ((LinearMap.toSpanSingleton ℝ E (ψ (WithLp.ofLp x).2)).coprod
      ((WithLp.ofLp x).1 • (fderiv ℝ ψ (WithLp.ofLp x).2 : W →ₗ[ℝ] E)) ∘ₗ
      (WithLp.linearEquiv 2 ℝ (ℝ × W)).toLinearMap).toContinuousLinearMap x := by
    intro x hx
    have h := ((WithLp.fstL 2 ℝ ℝ W).hasFDerivAt (x := x)).smul
      ((hd _ hx.2).hasFDerivAt.comp x (WithLp.sndL 2 ℝ ℝ W).hasFDerivAt)
    refine h.congr_fderiv ?_
    ext y
    simp [add_comm]
  have hJ : ∀ x ∈ S, (fderiv ℝ Φ x).normDet =
      (WithLp.ofLp x).1 ^ k * (fderiv ℝ ψ (WithLp.ofLp x).2).normDet := by
    intro x hx
    rw [(hΦ x hx).fderiv, LinearMap.coe_toContinuousLinearMap,
      LinearMap.normDet_toSpanSingleton_coprod (hnorm _ hx.2), LinearMap.normDet_smul,
      Real.norm_of_nonneg hx.1.1.le]
    intro u
    rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, inner_smul_right, horth _ hx.2,
      mul_zero]
  have hΦinj : ∀ x ∈ S, Injective (fderiv ℝ Φ x) := by
    intro x hx
    have hψ' : (fderiv ℝ ψ (WithLp.ofLp x).2).normDet ≠ 0 := fun h =>
      LinearMap.normDet_eq_zero_iff_ker_ne_bot.1 h (LinearMap.ker_eq_bot.2 (hinj _ hx.2))
    have hne : (fderiv ℝ Φ x).normDet ≠ 0 := by
      rw [hJ x hx]
      exact mul_ne_zero (pow_ne_zero _ hx.1.1.ne') hψ'
    exact LinearMap.ker_eq_bot.1 (not_not.1 (mt LinearMap.normDet_eq_zero_iff_ker_ne_bot.2 hne))
  have hΦs : InjOn Φ S := by
    intro x hx x' hx' h
    -- The radius is recovered as the norm, and then the point of `s` by injectivity of `ψ`.
    have ht : (WithLp.ofLp x).1 = (WithLp.ofLp x').1 := by
      have h' := congrArg norm h
      simp only [Φ, norm_smul, Real.norm_eq_abs, hnorm _ hx.2, hnorm _ hx'.2, mul_one,
        abs_of_pos hx.1.1, abs_of_pos hx'.1.1] at h'
      exact h'
    have hw : (WithLp.ofLp x).2 = (WithLp.ofLp x').2 := by
      refine hψs hx.2 hx'.2 (smul_right_injective E hx.1.1.ne' ?_)
      simpa only [Φ, ← ht] using h
    exact WithLp.ofLp_injective 2 (Prod.ext ht hw)
  have himage : Φ '' S = Ioo (0 : ℝ) 1 • (ψ '' s) := by
    rw [show Φ = (fun p : ℝ × W => p.1 • ψ p.2) ∘ WithLp.ofLp from rfl, image_comp,
      image_preimage_eq _ (WithLp.ofLp_surjective 2), image_prod (f := fun t w => t • ψ w),
      ← image2_image_right, image2_smul]
  have hrank : finrank ℝ (WithLp 2 (ℝ × W)) = finrank ℝ E := by
    rw [(WithLp.linearEquiv 2 ℝ (ℝ × W)).finrank_eq, finrank_prod, finrank_self]
    omega
  have harea := lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hS
    (fun x hx => (hΦ x hx).differentiableAt) hΦinj hΦs
  have hJψ : Measurable fun w => ENNReal.ofReal (fderiv ℝ ψ w).normDet :=
    (ContinuousLinearMap.continuous_normDet.measurable.comp (measurable_fderiv ℝ ψ)).ennreal_ofReal
  have hpow : Measurable fun t : ℝ => ENNReal.ofReal (t ^ k) :=
    (measurable_id.pow_const k).ennreal_ofReal
  have hrad : ∫⁻ t in Ioo (0 : ℝ) 1, ENNReal.ofReal (t ^ k) = ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    have h := lintegral_ofReal_rpow_Ioo (s := k) (by linarith [k.cast_nonneg (α := ℝ)])
      zero_le_one
    simp_rw [Real.rpow_natCast] at h
    rw [h, Real.one_rpow, one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
    norm_cast
  have hF : Measurable fun p : ℝ × W =>
      ENNReal.ofReal (p.1 ^ k) * ENNReal.ofReal (fderiv ℝ ψ p.2).normDet :=
    (hpow.comp measurable_fst).mul (hJψ.comp measurable_snd)
  -- Separate the radial and spherical variables by Fubini–Tonelli, and apply the area formula
  -- to `ψ`.
  rw [hrank, InnerProductSpace.euclideanHausdorffMeasure_eq_volume, himage,
    setLIntegral_congr_fun hS (fun x hx => by
      rw [hJ x hx, ENNReal.ofReal_mul (pow_nonneg hx.1.1.le _)]),
    (WithLp.volume_preserving_ofLp ℝ W).setLIntegral_comp_preimage
      (measurableSet_Ioo.prod hs) hF,
    Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_mul hpow.aemeasurable
      hJψ.aemeasurable, hrad,
    lintegral_normDet_fderiv_eq_euclideanHausdorffMeasure_image hs hd hinj hψs] at harea
  rw [← harea, ← hdim, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- The cone formula for a measurable set of the unit sphere that avoids a point `v`, which is
parametrized by the inverse of stereographic projection from `v`. -/
private theorem euclideanHausdorffMeasure_image_coe_of_forall_ne {v : E} (hv : ‖v‖ = 1)
    {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) (hvs : ∀ x ∈ s, (x : E) ≠ v) :
    μHE[finrank ℝ E - 1] (((↑) : sphere (0 : E) 1 → E) '' s) =
      finrank ℝ E * volume (Ioo (0 : ℝ) 1 • (((↑) : sphere (0 : E) 1 → E) '' s)) := by
  set ψ := stereoInvFunAux v ∘ ((↑) : (ℝ ∙ v)ᗮ → E)
  set A := ((↑) : sphere (0 : E) 1 → E) '' s
  have hnorm (w : (ℝ ∙ v)ᗮ) : ‖ψ w‖ = 1 := mem_sphere_zero_iff_norm.1 (stereoInvFunAux_mem hv w.2)
  have hd : Differentiable ℝ ψ :=
    (contDiff_stereoInvFunAux.comp (ℝ ∙ v)ᗮ.subtypeL.contDiff).differentiable one_ne_zero
  have hA : MeasurableSet A :=
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).measurableSet_image.2 hs
  have himage : ψ '' (ψ ⁻¹' A) = A := by
    refine image_preimage_eq_of_subset fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨stereoToFun v y, congrArg Subtype.val (stereo_left_inv hv (hvs y hy))⟩
  have hdim : finrank ℝ (ℝ ∙ v)ᗮ + 1 = finrank ℝ E := by
    have := (ℝ ∙ v).finrank_add_finrank_orthogonal
    rw [finrank_span_singleton (by rintro rfl; simp at hv)] at this
    omega
  have h := euclideanHausdorffMeasure_image_eq_finrank_mul_volume_Ioo_smul (ψ := ψ) hdim
    (hA.preimage hd.continuous.measurable) (fun w _ => Eventually.of_forall hnorm)
    (fun w _ => hd w) (fun w _ => injective_fderiv_stereoInvFunAux_comp_coe hv w)
    (Function.LeftInverse.injective (stereo_right_inv hv)).injOn
  rwa [himage, show finrank ℝ (ℝ ∙ v)ᗮ = finrank ℝ E - 1 by omega] at h

/-- Mathlib's surface measure `Measure.toSphere volume` on the unit sphere of an `n`-dimensional
real inner product space is normalized `(n - 1)`-dimensional Hausdorff measure. -/
theorem toSphere_volume_eq_comap_euclideanHausdorffMeasure :
    (volume : Measure E).toSphere = (μHE[finrank ℝ E - 1] : Measure E).comap (↑) := by
  rcases subsingleton_or_nontrivial E with hE | hE
  · have : IsEmpty (sphere (0 : E) 1) :=
      ⟨fun x => by simpa [Subsingleton.elim (x : E) 0] using x.2⟩
    ext s
    simp [Set.eq_empty_of_isEmpty s]
  have hemb :=
    MeasurableEmbedding.subtype_coe (isClosed_sphere (x := (0 : E)) (ε := 1)).measurableSet
  have key {v : E} (hv : ‖v‖ = 1) {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s)
      (hvs : ∀ x ∈ s, (x : E) ≠ v) :
      (volume : Measure E).toSphere s = (μHE[finrank ℝ E - 1] : Measure E).comap (↑) s := by
    rw [toSphere_apply' _ hs, hemb.comap_apply,
      euclideanHausdorffMeasure_image_coe_of_forall_ne hv hs hvs]
  -- Split a measurable set according to whether it contains `v`; each part avoids `v` or `-v`.
  obtain ⟨v, hv⟩ := exists_norm_eq E zero_le_one
  have hvneg : v ≠ -v := fun h => by
    have h₂ := congrArg (‖· + v‖) h
    simp only [neg_add_cancel, norm_zero, ← two_smul ℝ v, norm_smul, hv] at h₂
    norm_num at h₂
  ext s hs
  set t : Set (sphere (0 : E) 1) := {x | (x : E) = v}
  have ht : MeasurableSet t := measurableSet_eq_fun measurable_subtype_coe measurable_const
  rw [← measure_inter_add_sdiff s ht, ← measure_inter_add_sdiff s ht (μ := Measure.comap _ _)]
  congr 1
  · exact key (v := -v) (by simpa using hv) (hs.inter ht) fun x hx => hx.2.symm ▸ hvneg
  · exact key hv (hs.diff ht) fun x hx => hx.2

/-- Normalized `(n - 1)`-dimensional Hausdorff measure restricted to the unit sphere of an
`n`-dimensional real inner product space is the pushforward of Mathlib's surface measure
`Measure.toSphere volume`. -/
theorem euclideanHausdorffMeasure_restrict_sphere :
    (μHE[finrank ℝ E - 1] : Measure E).restrict (sphere 0 1) =
      (volume : Measure E).toSphere.map (↑) := by
  rw [toSphere_volume_eq_comap_euclideanHausdorffMeasure,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).map_comap, Subtype.range_coe]

/-- The unit sphere of an `n`-dimensional real inner product space has `(n - 1)`-dimensional
Hausdorff measure `n ω_n`, where `ω_n` is the volume of the unit ball. -/
theorem euclideanHausdorffMeasure_sphere_zero_one :
    μHE[finrank ℝ E - 1] (sphere (0 : E) 1) = finrank ℝ E * volume (ball (0 : E) 1) := by
  rw [← toSphere_apply_univ, toSphere_volume_eq_comap_euclideanHausdorffMeasure,
    (MeasurableEmbedding.subtype_coe isClosed_sphere.measurableSet).comap_apply, image_univ,
    Subtype.range_coe]

/-- The unit sphere of an `n`-dimensional real inner product space has `(n - 1)`-dimensional
Hausdorff measure `2 π ^ (n / 2) / Γ(n / 2)`. In dimension zero both sides vanish. -/
theorem euclideanHausdorffMeasure_sphere_zero_one_eq_ofReal :
    μHE[finrank ℝ E - 1] (sphere (0 : E) 1) =
      ENNReal.ofReal (2 * Real.pi ^ ((finrank ℝ E : ℝ) / 2) / Real.Gamma (finrank ℝ E / 2)) := by
  rw [euclideanHausdorffMeasure_sphere_zero_one]
  rcases (finrank ℝ E).eq_zero_or_pos with hn | hn
  · simp [hn, Real.Gamma_zero]
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hn
  have hn' : (0 : ℝ) < finrank ℝ E / 2 := by positivity
  -- The real identity `n · √π ^ n / Γ(n / 2 + 1) = 2 π ^ (n / 2) / Γ(n / 2)`.
  have hreal : (finrank ℝ E : ℝ) * (√Real.pi ^ finrank ℝ E / Real.Gamma (finrank ℝ E / 2 + 1)) =
      2 * Real.pi ^ ((finrank ℝ E : ℝ) / 2) / Real.Gamma (finrank ℝ E / 2) := by
    rw [Real.Gamma_add_one hn'.ne', Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast Real.pi_pos.le]
    field_simp
  rw [InnerProductSpace.volume_ball, ← hreal, ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  simp

/-- **The surface area of the unit sphere.** On a real inner product space of dimension `n`,
Mathlib's surface measure `Measure.toSphere volume` gives the unit sphere total mass
`2 π ^ (n / 2) / Γ(n / 2)`. In dimension zero the sphere is empty and both sides vanish. -/
theorem toSphere_volume_apply_univ :
    (volume : Measure E).toSphere univ =
      ENNReal.ofReal (2 * Real.pi ^ ((finrank ℝ E : ℝ) / 2) / Real.Gamma (finrank ℝ E / 2)) := by
  rw [toSphere_apply_univ, ← euclideanHausdorffMeasure_sphere_zero_one,
    euclideanHausdorffMeasure_sphere_zero_one_eq_ofReal]

/-- A sphere of radius `r > 0` in an `n`-dimensional real inner product space has
`(n - 1)`-dimensional Hausdorff measure `n ω_n r ^ (n - 1)`, where `ω_n` is the volume of the
unit ball. -/
theorem euclideanHausdorffMeasure_sphere (c : E) {r : ℝ} (hr : 0 < r) :
    μHE[finrank ℝ E - 1] (sphere c r) =
      finrank ℝ E * volume (ball (0 : E) 1) * ENNReal.ofReal r ^ (finrank ℝ E - 1) := by
  rw [← restrict_apply_univ, euclideanHausdorffMeasure_restrict_sphere_eq_smul_map _ c hr,
    Measure.smul_apply, map_apply (by fun_prop) MeasurableSet.univ, preimage_univ,
    restrict_apply_univ, euclideanHausdorffMeasure_sphere_zero_one, smul_eq_mul, mul_comm]

/-- The area `|Sⁿ|` of the unit round sphere `Sⁿ ⊆ ℝⁿ⁺¹`: the normalized `n`-dimensional Hausdorff
measure of the unit sphere of `EuclideanSpace ℝ (Fin (n + 1))`. -/
def roundSphereVolume (n : ℕ) : ℝ :=
  (μHE[n] (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toReal

/-- Unfolding lemma for `TauCeti.roundSphereVolume`. -/
theorem roundSphereVolume_def (n : ℕ) :
    roundSphereVolume n = (μHE[n] (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)).toReal :=
  (rfl)

omit [FiniteDimensional ℝ E] in
/-- The `n`-dimensional Hausdorff measure of the unit sphere of an `(n + 1)`-dimensional real
inner product space, in terms of the Gamma function. -/
private theorem euclideanHausdorffMeasure_sphere_eq_ofReal_Gamma {n : ℕ}
    (hE : finrank ℝ E = n + 1) :
    μHE[n] (sphere (0 : E) 1) =
      ENNReal.ofReal (2 * Real.pi ^ (((n : ℝ) + 1) / 2) / Real.Gamma (((n : ℝ) + 1) / 2)) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have h := euclideanHausdorffMeasure_sphere_zero_one_eq_ofReal (E := E)
  rw [hE, Nat.add_sub_cancel] at h
  exact_mod_cast h

/-- **The area of the unit round sphere**: `|Sⁿ| = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`. -/
theorem roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma (n : ℕ) :
    roundSphereVolume n =
      2 * Real.pi ^ (((n : ℝ) + 1) / 2) / Real.Gamma (((n : ℝ) + 1) / 2) := by
  rw [roundSphereVolume_def, euclideanHausdorffMeasure_sphere_eq_ofReal_Gamma
    finrank_euclideanSpace_fin, ENNReal.toReal_ofReal (by positivity)]

/-- The unit round sphere has positive area. -/
theorem roundSphereVolume_pos (n : ℕ) : 0 < roundSphereVolume n := by
  rw [roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma]
  positivity

omit [FiniteDimensional ℝ E] in
/-- The unit sphere of every real inner product space of dimension `n + 1` has normalized
`n`-dimensional Hausdorff measure `|Sⁿ|`. In particular, this measure is finite. -/
theorem euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume {n : ℕ}
    (hE : finrank ℝ E = n + 1) :
    μHE[n] (sphere (0 : E) 1) = ENNReal.ofReal (roundSphereVolume n) := by
  rw [euclideanHausdorffMeasure_sphere_eq_ofReal_Gamma hE,
    roundSphereVolume_eq_two_mul_pi_rpow_div_Gamma]

end TauCeti
