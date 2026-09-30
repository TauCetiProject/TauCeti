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
* `TauCeti.RiemannianIsometry.toDiffeomorph_tangent_apply`: the tangent-bundle lift has this
  fibrewise linear-isometry equivalence as its fibre map.
* `TauCeti.RiemannianIsometry.inner_mpullback`: pulling back vector fields along a Riemannian
  isometry preserves their pointwise inner products.
-/

public section

open Bundle Manifold VectorField
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.RiemannianIsometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

/-- The differential of a smooth Riemannian isometry at a point, as a linear isometric
equivalence of tangent spaces. Its underlying linear equivalence is Mathlib's
`Diffeomorph.mfderivToContinuousLinearEquiv`, bundled isometrically with Mathlib's
`LinearEquiv.isometryOfInner`. -/
def mfderivToLinearIsometryEquiv (Φ : RiemannianIsometry I J M N) (x : M) :
    TangentSpace I x ≃ₗᵢ[ℝ] TangentSpace J (Φ x) :=
  LinearEquiv.isometryOfInner
    (Φ.toDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv
    fun v w ↦ by
      have he : (Φ.toDiffeomorph.mfderivToContinuousLinearEquiv (by simp) x :
          TangentSpace I x →L[ℝ] TangentSpace J (Φ x)) =
          mfderiv I J Φ.toDiffeomorph x :=
        Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ.toDiffeomorph (by simp)
      exact (congrArg₂ (inner ℝ) (DFunLike.congr_fun he v) (DFunLike.congr_fun he w)).trans
        (Φ.inner_mfderiv x v w)

/-- The underlying function of `mfderivToLinearIsometryEquiv` is the manifold differential. -/
@[simp]
theorem coe_mfderivToLinearIsometryEquiv (Φ : RiemannianIsometry I J M N) (x : M) :
    ⇑(Φ.mfderivToLinearIsometryEquiv x) = fun v ↦ mfderiv I J Φ x v := by
  ext v
  exact DFunLike.congr_fun
    (Diffeomorph.mfderivToContinuousLinearEquiv_coe Φ.toDiffeomorph (by simp)) v

/-- Applying `mfderivToLinearIsometryEquiv` is the same as applying the manifold differential. -/
@[simp]
theorem mfderivToLinearIsometryEquiv_apply (Φ : RiemannianIsometry I J M N) (x : M)
    (v : TangentSpace I x) :
    Φ.mfderivToLinearIsometryEquiv x v = mfderiv I J Φ x v :=
  congrFun (coe_mfderivToLinearIsometryEquiv Φ x) v

/-- The inverse of the differential equivalence is the differential of the inverse Riemannian
isometry at `Φ x`. -/
@[simp]
theorem mfderivToLinearIsometryEquiv_symm_apply (Φ : RiemannianIsometry I J M N) (x : M)
    (v : TangentSpace J (Φ x)) :
    (Φ.mfderivToLinearIsometryEquiv x).symm v =
      mfderiv J I Φ.symm (Φ x) v := by
  apply (Φ.mfderivToLinearIsometryEquiv x).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  erw [mfderivToLinearIsometryEquiv_apply]
  rw [coe_symm]
  exact (Diffeomorph.mfderiv_apply_mfderiv_symm_apply
    Φ.toDiffeomorph (by simp) x v).symm

/-- The tangent-bundle lift of a Riemannian isometry uses its fibrewise linear isometric
equivalence on tangent vectors. -/
theorem toDiffeomorph_tangent_apply [IsManifold I 1 M] [IsManifold J 1 N]
    (Φ : RiemannianIsometry I J M N) (z : TangentBundle I M) :
    Φ.toDiffeomorph.tangent z =
      TotalSpace.mk' F (Φ z.1) (Φ.mfderivToLinearIsometryEquiv z.1 z.2) := by
  rw [Diffeomorph.coe_tangent, mfderivToLinearIsometryEquiv_apply]
  rfl

/-- Pulling back vector fields along a Riemannian isometry preserves their pointwise inner
products. -/
@[simp]
theorem inner_mpullback (Φ : RiemannianIsometry I J M N) (Y Z : Π y : N, TangentSpace J y)
    (x : M) :
    inner ℝ (mpullback I J Φ Y x) (mpullback I J Φ Z x) = inner ℝ (Y (Φ x)) (Z (Φ x)) := by
  rw [← Φ.inner_mfderiv x]
  -- `⇑Φ.toDiffeomorph` is `⇑Φ` by definition (`coe_toDiffeomorph` is `rfl`).
  exact congrArg₂ (inner ℝ) (Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) Y x)
    (Φ.toDiffeomorph.mfderiv_apply_mpullback (by simp) Z x)

end TauCeti.RiemannianIsometry

end
