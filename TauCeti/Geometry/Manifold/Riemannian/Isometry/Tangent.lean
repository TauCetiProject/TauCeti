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
* `TauCeti.RiemannianIsometry.mfderiv_image_ball`: the differential maps each ball of `T_x M` onto
  the ball of the same radius about the image of its centre.
* `TauCeti.mfderiv_smul_image_ball`, `TauCeti.mfderiv_smul_image_ball_of_smul_eq`: the same for the
  action of a group element whose differential preserves the metric; at a fixed point `x` of the
  element, every ball about the origin of `T_x M` is invariant.
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

/-- The differential of a Riemannian isometry at a point is injective. -/
theorem mfderiv_injective (Φ : RiemannianIsometry I J M N) (x : M) :
    Function.Injective (mfderiv I J Φ x) := by
  simpa only [coe_mfderivToLinearIsometryEquiv] using
    (Φ.mfderivToLinearIsometryEquiv x).injective

/-- The differential of a Riemannian isometry at a point is surjective onto the tangent space at
the image point. -/
theorem mfderiv_surjective (Φ : RiemannianIsometry I J M N) (x : M) :
    Function.Surjective (mfderiv I J Φ x) := by
  simpa only [coe_mfderivToLinearIsometryEquiv] using
    (Φ.mfderivToLinearIsometryEquiv x).surjective

/-- The differential of a Riemannian isometry at `x` maps the ball of radius `r` about `v` in
`T_x M` onto the ball of radius `r` about its image in `T_{Φ x} N`. -/
@[simp]
theorem mfderiv_image_ball (Φ : RiemannianIsometry I J M N) (x : M) (v : TangentSpace I x)
    (r : ℝ) :
    mfderiv I J Φ x '' Metric.ball v r = Metric.ball (mfderiv I J Φ x v) r := by
  simpa only [coe_mfderivToLinearIsometryEquiv, mfderivToLinearIsometryEquiv_apply] using
    (Φ.mfderivToLinearIsometryEquiv x).image_ball v r

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

end TauCeti.RiemannianIsometry

namespace TauCeti

open Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {G : Type*} [Group G] [MulAction G M] [ContMDiffConstSMul I ∞ G M] {a : G}

/-- If the differential of the action of `a` preserves the metric, then its differential at `x`
maps the ball of radius `r` about `v` in `T_x M` onto the ball of radius `r` about its image in
`T_{a • x} M`. -/
theorem mfderiv_smul_image_ball
    (ha : ∀ (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w)
    (x : M) (v : TangentSpace I x) (r : ℝ) :
    mfderiv I I (a • ·) x '' ball v r = ball (mfderiv I I (a • ·) x v) r := by
  have h := (RiemannianIsometry.constSMul a ha).mfderiv_image_ball x v r
  rw [RiemannianIsometry.coe_constSMul] at h
  exact h

/-- If the differential of the action of `a` preserves the metric and `a` fixes `x`, then its
differential at `x` leaves invariant every ball about the origin of `T_x M`. -/
theorem mfderiv_smul_image_ball_of_smul_eq
    (ha : ∀ (y : M) (v w : TangentSpace I y),
      inner ℝ (mfderiv I I (a • ·) y v) (mfderiv I I (a • ·) y w) = inner ℝ v w)
    {x : M} (hx : a • x = x) (r : ℝ) :
    mfderiv I I (a • ·) x '' ball (0 : TangentSpace I x) r = ball (0 : TangentSpace I x) r := by
  have h := mfderiv_smul_image_ball ha x 0 r
  rw [map_zero, hx] at h
  exact h

end TauCeti

end
