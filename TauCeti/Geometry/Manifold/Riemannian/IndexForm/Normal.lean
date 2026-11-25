/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Tangential
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Metric

/-!
# The index form of the normal part of a field

Along a geodesic `γ`, write `J^⊥ = J - proj_{γ'} J` for the normal part of a field `J` along `γ`,
its orthogonal projection onto the orthogonal complement of the velocity. Covariant
differentiation commutes with this projection
(`TauCeti.Manifold.IsGeodesicCurveOn.alongCurveWithin_sub_starProjection_singleton`), and the
curvature term `⟪R(J, γ') γ', J⟫` does not see the tangential part of `J`. Hence the index-form
integrand of `J^⊥` is that of `J` minus `‖proj_{γ'} D_t J‖²`.

## Main results

* `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton` and
  `TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton`: the
  index-form integrand of the normal part of a field is that of the field minus the squared
  tangential part of its covariant derivative.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018),
  Chapter 10.
-/

public section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {t : ℝ}

/-- **The index form sees only the normal part, up to its tangential derivative.** Along a
geodesic on a preconnected parameter set, let `J^⊥ = J - proj_{γ'} J` be the normal part of a
field `J` whose coordinates are differentiable at `t`. Then the index-form integrand of `J^⊥`
against itself is that of `J` minus `‖proj_{γ'} D_t J‖²`, computed with derivatives within the
parameter set. -/
theorem IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton
    (h : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s) (ht : t ∈ s)
    (hJ : DifferentiableWithinAt ℝ (sectionCoord ℝ (F := E) γ J (γ t)) s t) :
    indexFormIntegrandWithin I γ
        (fun r ↦ J r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (J r))
        (fun r ↦ J r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (J r)) s t =
      indexFormIntegrandWithin I γ J J s t -
        ‖(ℝ ∙ curveVelocityWithin I γ s t).starProjection
          (alongCurveWithin (leviCivitaConnection I M) γ J s t)‖ ^ 2 := by
  rw [indexFormIntegrandWithin_def, indexFormIntegrandWithin_def,
    h.alongCurveWithin_sub_starProjection_singleton hs ht hJ]
  set v := curveVelocityWithin I γ s t
  set D := alongCurveWithin (leviCivitaConnection I M) γ J s t
  -- the projection of `J t` is a multiple of `v`, invisible to the curvature term
  have hproj : (ℝ ∙ v).starProjection (J t) = (inner ℝ v (J t) / ‖v‖ ^ 2) • v := by
    rw [Submodule.starProjection_singleton, RCLike.ofReal_real_eq_id, id_eq]
  rw [hproj, IsMetricCompatible.inner_curvatureTensor_sub_smul
    (isMetricCompatible_leviCivitaConnection (I := I) (M := M)) (J t) v]
  -- `D - proj D` is orthogonal to `proj D`
  have horth := Submodule.starProjection_inner_eq_zero (K := ℝ ∙ v) D
    ((ℝ ∙ v).starProjection D) (Submodule.starProjection_apply_mem _ D)
  rw [← real_inner_self_eq_norm_sq ((ℝ ∙ v).starProjection D)]
  rw [inner_sub_left] at horth
  simp only [inner_sub_left, inner_sub_right] at horth ⊢
  rw [real_inner_comm D ((ℝ ∙ v).starProjection D)]
  linarith

/-- The unrestricted form of
`TauCeti.Manifold.IsGeodesicCurveOn.indexFormIntegrandWithin_sub_starProjection_singleton`: along
a geodesic on a preconnected neighbourhood of `t`, the index-form integrand of the normal part
`J - proj_{γ'} J` of a field `J` with differentiable coordinates at `t` is that of `J` minus
`‖proj_{γ'} D_t J‖²`. -/
theorem IsGeodesicCurveOn.indexFormIntegrand_sub_starProjection_singleton
    (h : IsGeodesicCurveOn I γ s) (hs : IsPreconnected s) (hst : s ∈ 𝓝 t)
    (hJ : DifferentiableAt ℝ (sectionCoord ℝ (F := E) γ J (γ t)) t) :
    indexFormIntegrand I γ
        (fun r ↦ J r - (ℝ ∙ curveVelocity I γ r).starProjection (J r))
        (fun r ↦ J r - (ℝ ∙ curveVelocity I γ r).starProjection (J r)) t =
      indexFormIntegrand I γ J J t -
        ‖(ℝ ∙ curveVelocity I γ t).starProjection
          (alongCurve (leviCivitaConnection I M) γ J t)‖ ^ 2 := by
  -- near `t`, derivatives within `s` are unrestricted derivatives
  have hfield : ∀ᶠ r in 𝓝 t,
      HEq (J r - (ℝ ∙ curveVelocity I γ r).starProjection (J r))
        (J r - (ℝ ∙ curveVelocityWithin I γ s r).starProjection (J r)) := by
    filter_upwards [eventually_mem_nhds_iff.2 hst] with r hr
    rw [curveVelocityWithin_of_mem_nhds hr]
  rw [indexFormIntegrand_congr (δ := γ) Filter.EventuallyEq.rfl hfield hfield,
    ← indexFormIntegrandWithin_of_mem_nhds hst, ← indexFormIntegrandWithin_of_mem_nhds hst,
    h.indexFormIntegrandWithin_sub_starProjection_singleton hs (mem_of_mem_nhds hst)
      (hJ.differentiableWithinAt), curveVelocityWithin_of_mem_nhds hst,
    alongCurveWithin_of_mem_nhds _ γ J hst]


end TauCeti.Manifold
