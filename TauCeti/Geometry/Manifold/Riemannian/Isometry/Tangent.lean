/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Basic
public import TauCeti.Geometry.Manifold.Diffeomorph.Tangent
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Tangent maps of Riemannian isometries

The differential of a smooth Riemannian isometry at each point is a linear isometric equivalence
of tangent spaces. Its inverse is the differential of the inverse Riemannian isometry. Together
with the tangent-bundle diffeomorphism `Diffeomorph.tangent`, this is the tangent-level transport
used for initial velocities and velocity lifts of curves.

## Main definitions and results

* `TauCeti.RiemannianIsometry.mfderivToLinearIsometryEquiv`: the differential as a linear
  isometric equivalence between tangent spaces.
* `TauCeti.RiemannianIsometry.mfderivToLinearIsometryEquiv_symm_apply`: the inverse equivalence is
  the differential of the inverse isometry.
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold J ∞ N] [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- The differential of a smooth Riemannian isometry at a point, as a linear isometric
equivalence of tangent spaces. Its underlying linear equivalence is Mathlib's
`Diffeomorph.mfderivToContinuousLinearEquiv`. -/
def mfderivToLinearIsometryEquiv (Φ : RiemannianIsometry I J M N) (x : M) :
    TangentSpace I x ≃ₗᵢ[ℝ] TangentSpace J (Φ x) where
  toLinearEquiv := (Φ.toDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
  norm_map' := by
    intro v
    have hv := DFunLike.congr_fun
      (Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ.toDiffeomorph (by simp)) v
    exact (congrArg norm hv).trans (Φ.norm_mfderiv x v)

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- The underlying map of `mfderivToLinearIsometryEquiv` is the manifold differential. -/
@[simp]
theorem mfderivToLinearIsometryEquiv_apply (Φ : RiemannianIsometry I J M N) (x : M)
    (v : TangentSpace I x) :
    Φ.mfderivToLinearIsometryEquiv x v = mfderiv I J Φ x v := by
  rw [mfderivToLinearIsometryEquiv]
  exact DFunLike.congr_fun
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ.toDiffeomorph (by simp)) v

omit [IsManifold I ∞ M] [IsManifold J ∞ N] in
/-- The inverse of the differential equivalence is the differential of the inverse Riemannian
isometry. -/
@[simp]
theorem mfderivToLinearIsometryEquiv_symm_apply (Φ : RiemannianIsometry I J M N) (x : M)
    (v : TangentSpace J (Φ x)) :
    (Φ.mfderivToLinearIsometryEquiv x).symm v =
      cast (congrArg (TangentSpace I) (Φ.toDiffeomorph.symm_apply_apply x))
        (mfderiv J I Φ.toDiffeomorph.symm (Φ x) v) := by
  apply (Φ.mfderivToLinearIsometryEquiv x).injective
  rw [LinearIsometryEquiv.apply_symm_apply, mfderivToLinearIsometryEquiv_apply]
  exact (Diffeomorph.mfderiv_apply_mfderiv_symm_apply
    Φ.toDiffeomorph (by simp) x v).symm

end TauCeti.RiemannianIsometry

end
