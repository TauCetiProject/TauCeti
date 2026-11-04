/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Exponential
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Hom
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Smoothness

/-!
# The initial third covariant derivative of a Jacobi field

If a Jacobi field `J` vanishes at `a`, then
`D³J(a) = -R(DJ(a), γ'(a)) γ'(a)`. In particular the radial Jacobi field
`J(t) = d(exp_p)_(t v) (t w)` has third covariant derivative `-R(w,v)v` at zero.
These identities identify the first curvature correction in the initial jet of
an exponential variation, before taking Taylor remainders or choosing a parallel frame.

We use the native Jacobi equation and smoothness of its curvature coefficient.
The product rule at a zero of a field eliminates the derivative of that coefficient.
The central inputs are `CovariantDerivative.contMDiff_curvatureTensorCLM` and
`isJacobiFieldOn_mfderiv_riemannianExp`.
All derivatives are within the stated parameter set, so the general formula also
applies at endpoints of nondegenerate closed intervals. No completeness is required.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 7 and 10
  (curvature convention, Jacobi equation and exponential variations).
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a : ℝ}

/-- The curvature coefficient of the Jacobi equation is a smooth endomorphism along a geodesic. -/
private theorem IsGeodesicCurveOn.contMDiffOn_jacobiOperator
    (hγ : IsGeodesicCurveOn I γ s) :
    ContMDiffOn 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun r ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (γ r)
        ((((leviCivitaConnection I M).curvatureTensorCLM
          (V := fun x : M ↦ TangentSpace I x)
          (fiberNorm := fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x))) (γ r)).flip
          (curveVelocityWithin I γ s r)).flip (curveVelocityWithin I γ s r))) s := by
  -- Cache the iterated hom-fibre instances, as in the curvature smoothness theorem.
  let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
  let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
  let _ : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ inferInstance
  let _ : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ inferInstance
  let _ : ∀ x : M, NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ inferInstance
  let _ : ∀ x : M, NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
    fun x ↦ inferInstance
  have hvel : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent ∞
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ s r)) s := by
    simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ s)] using
      hγ.contMDiffOn_curveVelocityLiftWithin_infty
  have hR := (contMDiff_curvatureTensorCLM (F := E)
    (V := fun x : M ↦ TangentSpace I x)
    (fiberNorm := fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x)))
    (leviCivitaConnection I M)).comp_contMDiffOn hγ.contMDiffOn_infty
  intro r hr
  have hswap := ContMDiffWithinAt.clm_bundle_flip (F₁ := E) (F₂ := E) (F₃ := E →L[ℝ] E)
    (V₁ := TangentSpace I) (V₂ := TangentSpace I)
    (V₃ := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (hR r hr)
  have hfirst := ContMDiffWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] E →L[ℝ] E)
    (E₁ := TangentSpace I)
    (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    hswap (hvel r hr)
  have hswap' := ContMDiffWithinAt.clm_bundle_flip (F₁ := E) (F₂ := E) (F₃ := E)
    (V₁ := TangentSpace I) (V₂ := TangentSpace I) (V₃ := TangentSpace I) hfirst
  exact ContMDiffWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] E)
    (E₁ := TangentSpace I) (E₂ := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    hswap' (hvel r hr)

/-- At a zero of a Jacobi field, its third covariant derivative is
`D³J = -R(DJ, γ')γ'`. Derivatives are taken within the same parameter set. -/
theorem IsJacobiFieldOn.alongCurveWithin_three_of_eq_zero
    (hJ : IsJacobiFieldOn I γ J s) (ha : a ∈ s) (hzero : J a = 0) :
    alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ J s) s) s a =
      -(leviCivitaConnection I M).curvatureTensor (γ a)
        (alongCurveWithin (leviCivitaConnection I M) γ J s a)
        (curveVelocityWithin I γ s a) (curveVelocityWithin I γ s a) := by
  let A := fun r ↦ (((leviCivitaConnection I M).curvatureTensorCLM
          (V := fun x : M ↦ TangentSpace I x)
          (fiberNorm := fun x ↦ inferInstanceAs (NormedAddCommGroup (TangentSpace I x))) (γ r)).flip
    (curveVelocityWithin I γ s r)).flip (curveVelocityWithin I γ s r)
  have hA := (hJ.isGeodesicCurveOn.contMDiffOn_jacobiOperator a ha).mdifferentiableWithinAt
    (by simp)
  have hprod := alongCurveWithin_clm_apply_of_eq_zero (leviCivitaConnection I M) γ J A
    (hJ.uniqueDiffOn a ha) hA ((hJ.contMDiffOn a ha).mdifferentiableWithinAt (by norm_num)) hzero
  have heq : ∀ r ∈ s, alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ J s) s r = (-1 : ℝ) • A r (J r) := by
    intro r hr
    simpa only [A, ContinuousLinearMap.flip_apply, curvatureTensorCLM_apply, neg_one_smul] using
      hJ.alongCurveWithin_alongCurveWithin_eq hr
  rw [alongCurveWithin_congr _ γ _
    (Filter.mem_of_superset self_mem_nhdsWithin (heq ·)) (heq a ha),
    alongCurveWithin_const_smul, hprod]
  simp only [A, ContinuousLinearMap.flip_apply, curvatureTensorCLM_apply, neg_one_smul]

/-- The radial exponential Jacobi field `t ↦ d(exp_p)_(t v) (t w)` has third covariant
derivative `-R(w,v)v` at zero, with the native curvature sign convention. -/
theorem alongCurveWithin_three_mfderiv_riemannianExp_zero (p : M) (v w : TangentSpace I p) :
    let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
    let J := fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w)
    let s := geodesicInterval I M p v
    alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ J s) s) s 0 =
      -(leviCivitaConnection I M).curvatureTensor p w v v := by
  dsimp only
  have h := (isJacobiFieldOn_mfderiv_riemannianExp p v w).alongCurveWithin_three_of_eq_zero
    zero_mem_geodesicInterval (by
      rw [zero_smul ℝ w]
      exact (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) ((0 : ℝ) • v)).map_zero)
  simp only [alongCurveWithin_mfderiv_riemannianExp_zero,
    curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval),
    curveVelocity_riemannianExp_smul_zero] at h
  -- Move only the curvature's base point; the field remains in the fibre over the radial curve.
  refine h.trans ?_
  exact congrArg (fun q : M ↦ (-(leviCivitaConnection I M).curvatureTensor q w v v : E))
    ((congrArg (riemannianExp I M p) (zero_smul ℝ v)).trans (riemannianExp_zero p))

end TauCeti.Manifold
