/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Jacobi.Jet
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.AlongCurve
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Derivative.Smoothness
import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongCurve.Hom
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Fourth covariant derivatives at a zero of a Jacobi field

Along a geodesic with velocity `T`, differentiating the Jacobi equation gives
`D³J = -(∇_T R)(J,T)T - R(DJ,T)T`. At a zero of `J`, one more derivative gives
`D⁴J = -2(∇_T R)(DJ,T)T`. In particular the radial exponential variation has
fourth derivative `-2(∇_v R)(w,v)v` at the origin.

These are exact covariant derivatives on the original tangent fibres. They identify the
curvature-derivative term needed to compute cubic normal-coordinate metric coefficients;
no Taylor remainder or metric expansion is asserted here. Derivatives remain within the
parameter set, so the formulas include endpoints of nondegenerate closed intervals.
No completeness, nonzero speed or orthogonality assumption is required.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 7 and 10.
* The calculation uses the native `IsJacobiFieldOn` equation,
  `CovariantDerivative.alongCurveWithin_curvatureTensor`, and
  `CovariantDerivative.contMDiff_derivCurvatureTensorCLM`.
-/

public section

open Bundle CovariantDerivative Filter Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {γ : ℝ → M} {J : ∀ t, TangentSpace I (γ t)} {s : Set ℝ} {a : ℝ}

/-- The third covariant derivative of a Jacobi field along a geodesic is
`-(∇_T R)(J,T)T - R(DJ,T)T`, with `T` its velocity. -/
theorem IsJacobiFieldOn.alongCurveWithin_three (hJ : IsJacobiFieldOn I γ J s)
    (ha : a ∈ s) :
    alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ J s) s) s a =
      -(leviCivitaConnection I M).derivCurvatureTensor (leviCivitaConnection I M) (γ a)
          (curveVelocityWithin I γ s a) (J a)
          (curveVelocityWithin I γ s a) (curveVelocityWithin I γ s a) -
        (leviCivitaConnection I M).curvatureTensor (γ a)
          (alongCurveWithin (leviCivitaConnection I M) γ J s a)
          (curveVelocityWithin I γ s a) (curveVelocityWithin I γ s a) := by
  let cov := leviCivitaConnection I M
  let T := curveVelocityWithin I γ s
  have hT := differentiableWithinAt_sectionCoord_curveVelocityWithin γ hJ.uniqueDiffOn
    hJ.isGeodesicCurveOn.contMDiffOn ha
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ a))
  have hDT : alongCurveWithin cov γ T s a = 0 :=
    by simpa only [accelerationWithin_def] using
      hJ.isGeodesicCurveOn.accelerationWithin_eq_zero a ha
  have heq (r : ℝ) (hr : r ∈ s) : alongCurveWithin cov γ
      (alongCurveWithin cov γ J s) s r =
        (-1 : ℝ) • cov.curvatureTensor (γ r) (J r) (T r) (T r) := by
    simpa only [neg_one_smul] using hJ.alongCurveWithin_alongCurveWithin_eq hr
  rw [alongCurveWithin_congr cov γ _
    (Filter.mem_of_superset self_mem_nhdsWithin (heq ·)) (heq a ha), alongCurveWithin_const_smul,
    cov.alongCurveWithin_curvatureTensor (hJ.uniqueDiffOn a ha)
      (hJ.isGeodesicCurveOn.mdifferentiableOn a ha)
      (hJ.differentiableWithinAt_sectionCoord ha) hT hT]
  simp only [T, cov] at hDT ⊢
  simp only [hDT, map_zero, LinearMap.zero_apply, add_zero, neg_one_smul, neg_add_rev]
  abel

/-- The coefficient `J ↦ (∇_T R)(J,T)T` has a differentiable lift along a geodesic. -/
private theorem IsGeodesicCurveOn.mdifferentiableWithinAt_derivJacobiOperator
    (hγ : IsGeodesicCurveOn I γ s) (ha : a ∈ s) :
    -- Cache the operator-space norms while elaborating the statement as well as its proof.
    let _ : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
    let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E) := inferInstance
    let _ : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
    let _ : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] E →L[ℝ] E) := inferInstance
    let _ : ∀ x : M, NormedAddCommGroup (TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun _ ↦ inferInstance
    let _ : ∀ x : M, NormedSpace ℝ (TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun _ ↦ inferInstance
    let _ : ∀ x : M, NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun _ ↦ inferInstance
    let _ : ∀ x : M, NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun _ ↦ inferInstance
    let _ : ∀ x : M, NormedAddCommGroup
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun _ ↦ inferInstance
    let _ : ∀ x : M, NormedSpace ℝ
      (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun _ ↦ inferInstance
    -- Fix the hom-fibre additive instances to avoid repeated expensive unification.
    let _ : ∀ x : M, AddCommMonoid
        (TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun x ↦ (inferInstance : NormedAddCommGroup
        (TangentSpace I x →L[ℝ] TangentSpace I x)).toAddCommMonoid
    let _ : ∀ x : M, AddCommMonoid
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun x ↦ (inferInstance : NormedAddCommGroup
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)).toAddCommMonoid
    let _ : ∀ x : M, AddCommMonoid
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x) :=
      fun x ↦ (inferInstance : NormedAddCommGroup
        (TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
          TangentSpace I x)).toAddCommMonoid
    MDifferentiableWithinAt 𝓘(ℝ, ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] E))
      (fun r ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) (γ r)
        (((((leviCivitaConnection I M).derivCurvatureTensorCLM
          (leviCivitaConnection I M) (γ r)) (curveVelocityWithin I γ s r)).flip
          (curveVelocityWithin I γ s r)).flip (curveVelocityWithin I γ s r))) s a := by
  intro normEnd spaceEnd normTwo spaceTwo normThree spaceThree
    normFiberEnd spaceFiberEnd normFiberTwo spaceFiberTwo normFiberThree spaceFiberThree
    monoidEnd monoidTwo monoidThree
  have hvel : ContMDiffWithinAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (γ r) (curveVelocityWithin I γ s r)) s a := by
    simpa only [funext (curveVelocityLiftWithin_apply (I := I) γ s)] using
      (hγ.contMDiffOn.contMDiffOn_curveVelocityLiftWithin (m := 1) (by norm_num)
        hγ.uniqueDiffOn.uniqueMDiffOn) a ha
  have hR := ((leviCivitaConnection I M).contMDiff_derivCurvatureTensorCLM
    (leviCivitaConnection I M)).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp) |>.contMDiffAt
    |>.comp_contMDiffWithinAt a ((hγ.contMDiffOn a ha).of_le (by norm_num))
  simp only [Function.comp_def] at hR
  have hfirst := ContMDiffWithinAt.clm_bundle_apply
    (F₁ := E) (F₂ := E →L[ℝ] E →L[ℝ] E →L[ℝ] E)
    (E₁ := TangentSpace I)
    (E₂ := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
      TangentSpace I x →L[ℝ] TangentSpace I x) hR hvel
  have hswap := ContMDiffWithinAt.clm_bundle_flip
    (F₁ := E) (F₂ := E) (F₃ := E →L[ℝ] E)
    (V₁ := TangentSpace I) (V₂ := TangentSpace I)
    (V₃ := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x) hfirst
  have hsecond := ContMDiffWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] E →L[ℝ] E)
    (E₁ := TangentSpace I)
    (E₂ := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] TangentSpace I x)
    hswap hvel
  have hswap' := ContMDiffWithinAt.clm_bundle_flip (F₁ := E) (F₂ := E) (F₃ := E)
    (V₁ := TangentSpace I) (V₂ := TangentSpace I) (V₃ := TangentSpace I) hsecond
  exact (ContMDiffWithinAt.clm_bundle_apply (F₁ := E) (F₂ := E →L[ℝ] E)
    (E₁ := TangentSpace I) (E₂ := fun x ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
    hswap' hvel).mdifferentiableWithinAt (by simp)

/-- At a zero of a Jacobi field, the fourth covariant derivative is
`D⁴J = -2(∇_T R)(DJ,T)T`. The formula holds within the parameter set, including endpoints. -/
theorem IsJacobiFieldOn.alongCurveWithin_four_of_eq_zero
    (hJ : IsJacobiFieldOn I γ J s) (ha : a ∈ s) (hzero : J a = 0) :
    alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ
          (alongCurveWithin (leviCivitaConnection I M) γ J s) s) s) s a =
      (-2 : ℝ) • (leviCivitaConnection I M).derivCurvatureTensor
        (leviCivitaConnection I M) (γ a) (curveVelocityWithin I γ s a)
        (alongCurveWithin (leviCivitaConnection I M) γ J s a)
        (curveVelocityWithin I γ s a) (curveVelocityWithin I γ s a) := by
  let cov := leviCivitaConnection I M
  let T := curveVelocityWithin I γ s
  let D := alongCurveWithin cov γ J s
  let B := fun r ↦ (((cov.derivCurvatureTensorCLM cov (γ r) (T r)).flip (T r)).flip (T r))
  let U := fun r ↦ B r (J r)
  let V := fun r ↦ cov.curvatureTensor (γ r) (D r) (T r) (T r)
  have hB := hJ.isGeodesicCurveOn.mdifferentiableWithinAt_derivJacobiOperator ha
  have hU := hB.clm_bundle_apply ((hJ.contMDiffOn a ha).mdifferentiableWithinAt (by norm_num))
  have hT := differentiableWithinAt_sectionCoord_curveVelocityWithin γ hJ.uniqueDiffOn
    hJ.isGeodesicCurveOn.contMDiffOn ha
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ a))
  have hV := cov.differentiableWithinAt_sectionCoord_curvatureTensor
    (hJ.isGeodesicCurveOn.mdifferentiableOn a ha)
    (hJ.differentiableWithinAt_sectionCoord_alongCurveWithin ha) hT hT
  have hDU : alongCurveWithin cov γ U s a =
      cov.derivCurvatureTensor cov (γ a) (T a) (D a) (T a) (T a) := by
    rw [alongCurveWithin_clm_apply_of_eq_zero cov γ J B (hJ.uniqueDiffOn a ha) hB
      ((hJ.contMDiffOn a ha).mdifferentiableWithinAt (by norm_num)) hzero]
    simp only [B, ContinuousLinearMap.flip_apply, derivCurvatureTensorCLM_apply, D]
  have hDT : alongCurveWithin cov γ T s a = 0 :=
    by simpa only [accelerationWithin_def] using
      hJ.isGeodesicCurveOn.accelerationWithin_eq_zero a ha
  have hDD : alongCurveWithin cov γ D s a = 0 := by
    simp [D, cov, hJ.alongCurveWithin_alongCurveWithin_eq ha, hzero]
  have hDV : alongCurveWithin cov γ V s a =
      cov.derivCurvatureTensor cov (γ a) (T a) (D a) (T a) (T a) := by
    rw [cov.alongCurveWithin_curvatureTensor (hJ.uniqueDiffOn a ha)
      (hJ.isGeodesicCurveOn.mdifferentiableOn a ha)
      (hJ.differentiableWithinAt_sectionCoord_alongCurveWithin ha) hT hT]
    simp only [D, cov] at hDT hDD ⊢
    simp [hDT, hDD, T]
  have heq (r : ℝ) (hr : r ∈ s) : alongCurveWithin cov γ
      (alongCurveWithin cov γ D s) s r = (-1 : ℝ) • (U r + V r) := by
    simpa only [U, V, B, ContinuousLinearMap.flip_apply, derivCurvatureTensorCLM_apply,
      neg_one_smul, neg_add_rev, sub_eq_add_neg, add_comm] using hJ.alongCurveWithin_three hr
  rw [alongCurveWithin_congr cov γ _
      (Filter.mem_of_superset self_mem_nhdsWithin (heq ·)) (heq a ha),
    alongCurveWithin_const_smul, alongCurveWithin_add cov γ U V s
      (TauCeti.Manifold.differentiableWithinAt_sectionCoord γ U hU
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) (γ a))) hV,
    hDU, hDV]
  simp only [neg_one_smul, neg_add_rev]
  module

/-- The radial exponential Jacobi field `J(t) = d(exp_p)_(tv)(tw)` has fourth covariant
derivative `-2(∇_v R)(w,v)v` at zero. The exponential is used on its natural geodesic interval. -/
theorem alongCurveWithin_four_mfderiv_riemannianExp_zero [I.Boundaryless]
    (p : M) (v w : TangentSpace I p) :
    let γ := fun t : ℝ ↦ riemannianExp I M p (t • v)
    let J := fun t ↦ mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) (t • v) (t • w)
    let s := geodesicInterval I M p v
    alongCurveWithin (leviCivitaConnection I M) γ
      (alongCurveWithin (leviCivitaConnection I M) γ
        (alongCurveWithin (leviCivitaConnection I M) γ
          (alongCurveWithin (leviCivitaConnection I M) γ J s) s) s) s 0 =
      (-2 : ℝ) • (leviCivitaConnection I M).derivCurvatureTensor
        (leviCivitaConnection I M) p v w v v := by
  dsimp only
  have h := (isJacobiFieldOn_mfderiv_riemannianExp p v w).alongCurveWithin_four_of_eq_zero
    zero_mem_geodesicInterval (by
      rw [zero_smul ℝ w]
      exact (mfderiv 𝓘(ℝ, TangentSpace I p) I (riemannianExp I M p) ((0 : ℝ) • v)).map_zero)
  simp only [alongCurveWithin_mfderiv_riemannianExp_zero,
    curveVelocityWithin_of_mem_nhds (isOpen_geodesicInterval.mem_nhds zero_mem_geodesicInterval),
    curveVelocity_riemannianExp_smul_zero] at h
  -- Transport the base point of the tensor while keeping the radial field's fibre intact.
  refine h.trans ?_
  exact congrArg (fun q : M ↦ ((-2 : ℝ) • (leviCivitaConnection I M).derivCurvatureTensor
    (leviCivitaConnection I M) q v w v v : E))
    ((congrArg (riemannianExp I M p) (zero_smul ℝ v)).trans (riemannianExp_zero p))

end TauCeti.Manifold
