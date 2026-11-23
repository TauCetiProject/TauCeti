/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Completeness
public import TauCeti.Geometry.Manifold.Flow.Complete
public import TauCeti.Geometry.Manifold.Riemannian.Laplacian

/-!
# Completeness of parallel gradients

A gradient with zero Hessian is a complete vector field on a geodesically complete manifold.
-/

public section

open Bundle CovariantDerivative FiberBundle Filter Function Set Topology
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I ∞ E (TangentSpace I : M → Type _)] {f : M → ℝ}

/-- On a geodesically complete Riemannian manifold, a zero-Hessian gradient is a complete field.
-/
theorem isCompleteVectorField_mgradient_of_hessian_eq_zero
    (hcomplete : ∀ x, IsGeodesicallyCompleteAt I M x)
    (hgrad : MDifferentiable I I.tangent (T% (mgradient I f)))
    (hzero : ∀ x (v w : TangentSpace I x), hessian I f x v w = 0) :
    IsCompleteVectorField (mgradient I f) := by
  apply isCompleteVectorField_of_forall_exists_isMIntegralCurve
  intro x
  let γ := maximalGeodesic I M x (mgradient I f x)
  have hgeo := isGeodesicCurveOnFrom_maximalGeodesic (I := I) x (mgradient I f x)
  have hdomain : expDomain I M x = univ := expDomain_eq_univ_iff.2 (hcomplete x)
  have hinterval : geodesicInterval I M x (mgradient I f x) = univ := by
    rw [geodesicInterval_eq_preimage_expDomain, hdomain, preimage_univ]
  rw [hinterval] at hgeo
  have hγ : ContMDiff 𝓘(ℝ) I 2 γ :=
    contMDiffOn_univ.1 hgeo.isGeodesicCurveOn.contMDiffOn
  have hbase : γ 0 = x := hgeo.base_eq
  have hinit : curveVelocity I γ 0 = mgradient I f (γ 0) := by
    have h := curveVelocityWithin_eq_of_hasMFDerivWithinAt
      (hgeo.hasMFDerivAt_zero (by simp)).hasMFDerivWithinAt uniqueDiffWithinAt_univ
    -- `curveVelocityWithin` is the scalar tangent identification of the differential.
    change curveVelocityWithin I γ univ 0 = mgradient I f x at h
    rw [curveVelocityWithin_univ] at h
    rw [hbase]
    exact h
  have hvel (t : ℝ) : curveVelocity I γ t = mgradient I f (γ t) := by
    apply (isMetricCompatible_leviCivitaConnection (M := M) I).eq_of_alongCurve_eq_zero
      isPreconnected_univ (fun r _ ↦ hγ.mdifferentiable (by norm_num) r)
      (fun r _ ↦ (hγ r).differentiableAt_sectionCoord_curveVelocity)
      (fun r _ ↦ differentiableAt_sectionCoord γ _
        ((hgrad (γ r)).comp r
          (hγ.mdifferentiable (by norm_num) r))
        (mem_baseSet_trivializationAt E (TangentSpace I) (γ r)))
      (fun r _ ↦ ?_) (fun r _ ↦ ?_) (mem_univ 0) (mem_univ t) hinit
    · rw [← acceleration_def]
      exact (isGeodesicCurve_iff.1 (isGeodesicCurveOn_univ.1 hgeo.isGeodesicCurveOn)).2 r
    · rw [alongCurve_pullback _ γ _
        (hasMFDerivAt_curveVelocity (hγ.mdifferentiable (by norm_num) r))
        (hgrad (γ r))]
      exact leviCivitaConnection_mgradient_eq_zero_of_hessian_eq_zero _ _ (hzero _ _)
  refine ⟨γ, hbase, fun t ↦ ?_⟩
  simpa only [hvel t] using hasMFDerivAt_curveVelocity (hγ.mdifferentiable (by norm_num) t)

end Complete

end TauCeti.Manifold
