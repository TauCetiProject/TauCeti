/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic

/-!
# The relative volume of two Riemannian metrics

Let `g` and `g'` be two Riemannian metrics on a manifold `M`, and let
`J = Bundle.ContMDiffRiemannianMetric.relativeVolumeDensity g g'` be the relative volume
density, so that `dV_{g'} = J dV_g`. The *relative volume* of `g'` with respect to `g` is

`V(g, g') = ∫ (J - 1) dV_g`.

On a compact manifold it is `Vol(g') - Vol(g)`. The integrand vanishes wherever `g'` agrees
with `g`, so the relative volume also makes sense for variations with compact support on
a noncompact manifold, where the total volumes may be infinite. The manifold `M` may have boundary
and corners, and no orientation is used.

Its dependence on a family of metrics is in
`TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Family`, the case of the metrics
induced by a family of immersions in
`TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Pullback`, and the case of a variation
with fixed compact support on a noncompact manifold in
`TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.CompactSupport`.

## Main definitions

* `Bundle.ContMDiffRiemannianMetric.relativeVolume`: the relative volume `∫ (J - 1) dV_g`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.contMDiffAt_relativeVolume_integrand`: the integrand
  `J(g₀, g_t) - 1` of the relative volume of a family of metrics is jointly `C^k` in `(t, x)`.
* `Bundle.ContMDiffRiemannianMetric.relativeVolume_eq_sub`: on a compact manifold the relative
  volume is the difference of the total volumes.
* `Bundle.ContMDiffRiemannianMetric.relativeVolume_add_relativeVolume`: on a compact manifold,
  relative volumes add up along a chain of metrics.
-/

public section

open Bundle MeasureTheory Set Function TauCeti
open scoped Manifold ContDiff Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {n n' : ℕ∞ω}

section RelativeVolume

variable [LindelofSpace M]

/-- The **relative volume** of a Riemannian metric `g'` with respect to a Riemannian metric `g`:
the integral `∫ (J - 1) dV_g` of the relative volume density `J` of `g'` with respect to `g`,
minus one, against the Riemannian volume of `g`. -/
def relativeVolume
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)) : ℝ :=
  ∫ x, (relativeVolumeDensity g g' x.ofWithMetric - 1) ∂riemannianVolume I (WithMetric g)

variable (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
  (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))

/-- The definition of the relative volume. -/
theorem relativeVolume_def :
    relativeVolume g g' =
      ∫ x, (relativeVolumeDensity g g' x.ofWithMetric - 1) ∂riemannianVolume I (WithMetric g) :=
  (rfl)

/-- The relative volume of a metric with respect to itself is zero. -/
@[simp]
theorem relativeVolume_self : relativeVolume g g = 0 := by
  simp [relativeVolume_def]

end RelativeVolume

section Integrand

variable {g₀ : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x)}
  {g : ℝ → ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x)} {t₀ : ℝ}

/-- **Joint regularity of the relative-volume integrand.** The integrand
`(t, x) ↦ J(g₀, g_t)(x) - 1` of the relative volume of a family of metrics `g_t` with respect to
a fixed metric `g₀`, on the copy of `M` carrying `g₀`, is `C^k` at `(t₀, x)` when the inner
products of `g₀` are `C^k` at `x` and those of `g_t` are `C^k` jointly in `(t, x)` at `(t₀, x)`. -/
theorem contMDiffAt_relativeVolume_integrand {k : ℕ∞ω} [IsManifold I (k + 1) M]
    {x : WithMetric g₀}
    (hg₀ : ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) k
      (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (g₀.inner x))
      x.ofWithMetric)
    (hg : ContMDiffAt (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) k
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2
        ((g p.1).inner p.2)) (t₀, x.ofWithMetric)) :
    ContMDiffAt (𝓘(ℝ).prod I) 𝓘(ℝ) k
      (uncurry fun (t : ℝ) (y : WithMetric g₀) ↦
        relativeVolumeDensity g₀ (g t) y.ofWithMetric - 1) (t₀, x) :=
  ((contMDiffAt_uncurry_relativeVolumeDensity hg₀ hg).comp (t₀, x) (contMDiffAt_fst.prodMk
      ((WithMetric.contMDiff_ofWithMetric (g := g₀)).contMDiffAt.comp _ contMDiffAt_snd))).sub
    contMDiffAt_const

end Integrand

section CompactSpace

variable [CompactSpace M] (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
  (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))

/-- **The relative volume on a compact manifold.** On a compact manifold, the relative volume of
`g'` with respect to `g` is the difference `Vol(g') - Vol(g)` of the total volumes. -/
theorem relativeVolume_eq_sub :
    relativeVolume g g' =
      riemannianTotalVolume I (WithMetric g') - riemannianTotalVolume I (WithMetric g) := by
  have hJ : Integrable (fun x : WithMetric g ↦ relativeVolumeDensity g g' x.ofWithMetric)
      (riemannianVolume I (WithMetric g)) := by
    simpa only [smul_eq_mul, mul_one] using
      (integrable_riemannianVolume_iff_integrable_relativeVolumeDensity_smul g g'
        fun _ ↦ (1 : ℝ)).1 (integrable_const 1)
  rw [relativeVolume_def, integral_sub hJ (integrable_const 1),
    riemannianTotalVolume_eq_integral_relativeVolumeDensity, integral_const_riemannianVolume,
    one_mul]

variable {n'' : ℕ∞ω} (g'' : ContMDiffRiemannianMetric I n'' E (fun x : M ↦ TangentSpace I x))

/-- On a compact manifold, relative volumes add up along a chain of three metrics. -/
theorem relativeVolume_add_relativeVolume :
    relativeVolume g g' + relativeVolume g' g'' = relativeVolume g g'' := by
  rw [relativeVolume_eq_sub, relativeVolume_eq_sub, relativeVolume_eq_sub]
  ring

end CompactSpace

end Bundle.ContMDiffRiemannianMetric
