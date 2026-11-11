/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.InvariantForm
public import TauCeti.Geometry.Lie.Exponential.Basic
public import TauCeti.Geometry.Lie.Interior
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Exponential
import TauCeti.Geometry.Manifold.Riemannian.LieGroup.BiInvariant

/-!
# Geodesics and the Lie exponential

For an ad-invariant left-invariant Riemannian metric on a finite-dimensional real Lie group,
the canonical integral curves of left-invariant vector fields are geodesics. In particular,
one-parameter subgroups are geodesics, and the Riemannian exponential at the identity agrees
with the Lie exponential. At any other base point it is its left translate, with the initial
velocity translated back to the identity.

The hypotheses are the left-invariance of the metric and the infinitesimal invariance of its
inner product at the identity. They apply to bi-invariant metrics without requiring the group
to be compact or connected.

## Main results

* `TauCeti.Manifold.isGeodesicCurve_mulInvariantIntegralCurve`: integral curves of invariant
  fields are geodesics.
* `TauCeti.Manifold.isGeodesicCurveOnFrom_mulInvariantIntegralCurve`: the same with prescribed
  initial point and velocity.
* `TauCeti.Manifold.riemannianExp_mulInvariantVectorField`: the Riemannian exponential is a
  left translate of the Lie exponential.
* `TauCeti.Manifold.riemannianExp_eq_mul_mulInvariantExp`: the formula for an arbitrary initial
  velocity, translated back to the identity.
* `TauCeti.Manifold.riemannianExp_one_eq_mulInvariantExp`: at the identity the tangent-space
  exponentials agree.
* `TauCeti.Manifold.riemannianExp_one_eq_lieExp`: the corresponding derivation-based identity.

## References

* A. Kirillov Jr., *An Introduction to Lie Groups and Lie Algebras*, Cambridge Studies in
  Advanced Mathematics 113 (2008), §3.11, Exercise 3.14(2).
-/

public section

noncomputable section

open Bundle CovariantDerivative Manifold Set VectorField
open scoped ContDiff Manifold

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  [T2Space G] [RiemannianBundle (fun g : G ↦ TangentSpace I g)]

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

private noncomputable local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

variable
  (hL : ∀ (g : G) (a b : TangentSpace I (1 : G)),
    inner ℝ (mulInvariantVectorField a g) (mulInvariantVectorField b g) = inner ℝ a b)
  (had : LinearMap.BilinForm.lieInvariant (TangentSpace I (1 : G))
    (innerₗ (TangentSpace I (1 : G))))

include hL had

section Curves

variable [IsContMDiffRiemannianBundle I 1 E (fun g : G ↦ TangentSpace I g)]

/-- Canonical integral curves of left-invariant fields are geodesics for an ad-invariant
left-invariant metric. -/
theorem isGeodesicCurve_mulInvariantIntegralCurve (a : TangentSpace I (1 : G)) (x : G) :
    IsGeodesicCurve I (mulInvariantIntegralCurve a x) := by
  have hγ := isMIntegralCurve_mulInvariantIntegralCurve a x
  have hvelocity : curveVelocity I (mulInvariantIntegralCurve a x) =
      fun t ↦ mulInvariantVectorField a (mulInvariantIntegralCurve a x t) := by
    funext t
    rw [← curveVelocityWithin_univ]
    exact curveVelocityWithin_eq_of_hasMFDerivWithinAt
      (hγ t).hasMFDerivWithinAt uniqueDiffWithinAt_univ
  refine isGeodesicCurve_iff.mpr ⟨(contMDiff_mulInvariantIntegralCurve a x).of_le (by simp), ?_⟩
  intro t
  rw [acceleration_def, hvelocity,
    alongCurve_pullback _ _ _ (hγ t)
      ((contMDiff_mulInvariantVectorField_infty a).mdifferentiableAt (by simp))]
  rw [(isLeviCivitaConnection_leviCivitaConnection I).apply_mulInvariantVectorField hL had]
  simp only [lie_self, smul_zero, mulInvariantVectorField_zero, Pi.zero_apply]

/-- An invariant integral curve is a geodesic with initial velocity the value of its generating
field at its initial point. -/
theorem isGeodesicCurveOnFrom_mulInvariantIntegralCurve
    (a : TangentSpace I (1 : G)) (x : G) :
    IsGeodesicCurveOnFrom I (mulInvariantIntegralCurve a x) univ x
      (mulInvariantVectorField a x) where
  isGeodesicCurveOn := isGeodesicCurveOn_univ.mpr
    (isGeodesicCurve_mulInvariantIntegralCurve hL had a x)
  zero_mem := mem_univ 0
  initial_eq := by
    rw [curveVelocityWithin_eq_of_hasMFDerivWithinAt
      ((isMIntegralCurve_mulInvariantIntegralCurve a x 0).hasMFDerivWithinAt)
      uniqueDiffWithinAt_univ, mulInvariantIntegralCurve_zero]

end Curves

section Exponential

variable [I.Boundaryless]
  [IsContMDiffRiemannianBundle I ∞ E (fun g : G ↦ TangentSpace I g)]

/-- The Riemannian exponential of an invariant field value is the left translate of the
tangent-space Lie exponential of its generator. -/
@[simp]
theorem riemannianExp_mulInvariantVectorField (a : TangentSpace I (1 : G)) (x : G) :
    riemannianExp I G x (mulInvariantVectorField a x) = x * mulInvariantExp a := by
  rw [riemannianExp_def,
    (isGeodesicCurveOnFrom_mulInvariantIntegralCurve hL had a x).eq_maximalGeodesic_of_univ,
    mulInvariantIntegralCurve_eq_const_mul]
  simp only [← mulInvariantExp_eq_mulInvariantIntegralCurve]

/-- The Riemannian exponential at `x` is the left translate of the Lie exponential, with the
initial velocity translated to the identity. -/
theorem riemannianExp_eq_mul_mulInvariantExp (x : G) (v : TangentSpace I x) :
    riemannianExp I G x v = x * mulInvariantExp (I := I) (mfderiv I I (x⁻¹ * ·) x v) := by
  simpa only [TauCeti.mulInvariantVectorField_mfderiv_inv_mul (I := I)] using
    riemannianExp_mulInvariantVectorField hL had (mfderiv I I (x⁻¹ * ·) x v) x

/-- At the identity the Riemannian exponential agrees with the tangent-space Lie exponential. -/
@[simp]
theorem riemannianExp_one_eq_mulInvariantExp (a : TangentSpace I (1 : G)) :
    riemannianExp I G 1 a = mulInvariantExp a := by
  simpa only [mulInvariantVectorField_one, one_mul] using
    riemannianExp_mulInvariantVectorField hL had a (1 : G)

/-- The Riemannian exponential at the identity agrees with the derivation-based Lie exponential
under the canonical identification of derivations with tangent vectors. -/
theorem riemannianExp_one_eq_lieExp (X : LeftInvariantDerivation I G) :
    riemannianExp I G 1
        (leftInvariantDerivationEquivGroupLieAlgebra (I := I) (G := G)
          BoundarylessManifold.isInteriorPoint X) = lieExp X := by
  rw [riemannianExp_one_eq_mulInvariantExp hL had, lieExp_eq_mulInvariantExp]

end Exponential

end TauCeti.Manifold
