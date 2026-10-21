/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Tangent

/-!
# Local Riemannian isometries

A *local Riemannian isometry* `f : M → N` is a smooth map whose differential at every point is an
invertible linear map preserving the Riemannian inner product. Unlike a Riemannian isometry
(`TauCeti.RiemannianIsometry`), it need not be injective or surjective: the inclusion of an open
submanifold carrying the restricted metric, the inclusion of one component of a disjoint union, and
a Riemannian covering map are all local Riemannian isometries.

Every local construction of Riemannian geometry is natural under local Riemannian isometries,
since pulling vector fields back along `f` only involves the differential of `f` at each point.
This file sets up the pointwise API used to transport the Levi-Civita connection and the curvature
along such maps.

## Main definitions and results

* `TauCeti.IsLocalRiemannianIsometry`: a smooth map with invertible differentials preserving the
  inner product.
* `TauCeti.IsLocalRiemannianIsometry.exists_linearIsometryEquiv_eq_mfderiv`: the differential at
  each point is a linear isometric equivalence of tangent spaces.
* `TauCeti.IsLocalRiemannianIsometry.mfderiv_apply_mpullback`: the differential sends a pulled-back
  vector field to the original field.
* `TauCeti.IsLocalRiemannianIsometry.inner_mpullback`: pulling back vector fields preserves their
  pointwise inner products.
* `TauCeti.IsLocalRiemannianIsometry.id` and `TauCeti.IsLocalRiemannianIsometry.comp`: the identity
  and composites.
* `TauCeti.RiemannianIsometry.isLocalRiemannianIsometry`: a Riemannian isometry is a local
  Riemannian isometry.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (local isometries).
-/

public section

open Bundle Manifold VectorField
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]

variable (I J) in
/-- A smooth map `f : M → N` between Riemannian manifolds is a local Riemannian isometry if its
differential at every point is an invertible continuous linear map preserving the inner product
of tangent vectors. -/
structure IsLocalRiemannianIsometry (f : M → N) : Prop where
  /-- A local Riemannian isometry is smooth. -/
  contMDiff : ContMDiff I J ∞ f
  /-- The differential of a local Riemannian isometry is invertible at every point. -/
  isInvertible_mfderiv (x : M) : (mfderiv I J f x).IsInvertible
  /-- The differential of a local Riemannian isometry preserves the inner product. -/
  inner_mfderiv (x : M) (v w : TangentSpace I x) :
    inner ℝ (mfderiv I J f x v) (mfderiv I J f x w) = inner ℝ v w

namespace IsLocalRiemannianIsometry

variable {f : M → N}

/-- A local Riemannian isometry is differentiable at each point. -/
protected theorem mdifferentiableAt (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    MDifferentiableAt I J f x :=
  hf.contMDiff.mdifferentiableAt (by simp) (x := x)

/-- The differential of a local Riemannian isometry at a point is injective. -/
theorem mfderiv_injective (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    Function.Injective (mfderiv I J f x) :=
  (hf.isInvertible_mfderiv x).bijective.1

/-- The differential of a local Riemannian isometry at a point is surjective onto the tangent
space at the image point. -/
theorem mfderiv_surjective (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    Function.Surjective (mfderiv I J f x) :=
  (hf.isInvertible_mfderiv x).bijective.2

/-- The differential of a local Riemannian isometry at a point is a linear isometric equivalence
of tangent spaces. -/
theorem exists_linearIsometryEquiv_eq_mfderiv (hf : IsLocalRiemannianIsometry I J f) (x : M) :
    ∃ e : TangentSpace I x ≃ₗᵢ[ℝ] TangentSpace J (f x), ∀ v, e v = mfderiv I J f x v := by
  obtain ⟨A, hA⟩ := hf.isInvertible_mfderiv x
  have hAv : ∀ v, A v = mfderiv I J f x v := fun v ↦ by rw [← hA, ContinuousLinearEquiv.coe_coe]
  refine ⟨LinearEquiv.isometryOfInner A.toLinearEquiv fun v w ↦ ?_, hAv⟩
  simpa only [ContinuousLinearEquiv.coe_toLinearEquiv, hAv] using hf.inner_mfderiv x v w

/-- The differential of a local Riemannian isometry sends the pullback of a vector field at `x` to
the value of the field at `f x`. -/
@[simp]
theorem mfderiv_apply_mpullback (hf : IsLocalRiemannianIsometry I J f)
    (V : Π y : N, TangentSpace J y) (x : M) :
    mfderiv I J f x (mpullback I J f V x) = V (f x) :=
  (hf.isInvertible_mfderiv x).self_apply_inverse _

/-- The pullback of a vector field along a local Riemannian isometry takes the value `v` at `x`
exactly when the field takes the value `df_x v` at `f x`. -/
theorem mpullback_apply_eq_iff (hf : IsLocalRiemannianIsometry I J f)
    (V : Π y : N, TangentSpace J y) {x : M} (v : TangentSpace I x) :
    mpullback I J f V x = v ↔ V (f x) = mfderiv I J f x v := by
  rw [← hf.mfderiv_apply_mpullback V x, (hf.mfderiv_injective x).eq_iff]

/-- Pulling back vector fields along a local Riemannian isometry preserves their pointwise inner
products. -/
@[simp]
theorem inner_mpullback (hf : IsLocalRiemannianIsometry I J f)
    (Y Z : Π y : N, TangentSpace J y) (x : M) :
    inner ℝ (mpullback I J f Y x) (mpullback I J f Z x) = inner ℝ (Y (f x)) (Z (f x)) := by
  rw [← hf.inner_mfderiv x, hf.mfderiv_apply_mpullback, hf.mfderiv_apply_mpullback]

section Regularity

variable [CompleteSpace E] [IsManifold I 2 M] [IsManifold J 2 N]

/-- Pulling back a differentiable vector field along a local Riemannian isometry gives a
differentiable vector field. -/
theorem mdifferentiableAt_mpullback (hf : IsLocalRiemannianIsometry I J f)
    {V : Π y : N, TangentSpace J y} {x : M} (hV : MDiffAt (T% V) (f x)) :
    MDiffAt (T% (mpullback I J f V)) x :=
  hV.mpullback_vectorField (hf.contMDiff.contMDiffAt) (hf.isInvertible_mfderiv x) (by simp)

/-- Pulling back a smooth vector field along a local Riemannian isometry gives a smooth vector
field. -/
theorem contMDiff_mpullback (hf : IsLocalRiemannianIsometry I J f)
    {V : Π y : N, TangentSpace J y} (hV : CMDiff ∞ (T% V)) :
    CMDiff ∞ (T% (mpullback I J f V)) :=
  hV.mpullback_vectorField hf.contMDiff hf.isInvertible_mfderiv (by simp)

end Regularity

variable (I M) in
/-- The identity map is a local Riemannian isometry. -/
protected theorem id : IsLocalRiemannianIsometry I I (id : M → M) where
  contMDiff := contMDiff_id
  isInvertible_mfderiv x := by
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  inner_mfderiv x v w := by
    simp only [mfderiv_id, ContinuousLinearMap.id_apply]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
  [RiemannianBundle (fun z : P ↦ TangentSpace K z)]

/-- The composite of two local Riemannian isometries is a local Riemannian isometry. -/
protected theorem comp {g : N → P} (hg : IsLocalRiemannianIsometry J K g)
    (hf : IsLocalRiemannianIsometry I J f) : IsLocalRiemannianIsometry I K (g ∘ f) where
  contMDiff := hg.contMDiff.comp hf.contMDiff
  isInvertible_mfderiv x := by
    rw [mfderiv_comp x (hg.mdifferentiableAt (f x)) (hf.mdifferentiableAt x)]
    exact (hg.isInvertible_mfderiv (f x)).comp (hf.isInvertible_mfderiv x)
  inner_mfderiv x v w := by
    rw [mfderiv_comp_apply x (hg.mdifferentiableAt (f x)) (hf.mdifferentiableAt x),
      mfderiv_comp_apply x (hg.mdifferentiableAt (f x)) (hf.mdifferentiableAt x),
      hg.inner_mfderiv, hf.inner_mfderiv]

end IsLocalRiemannianIsometry

/-- A smooth Riemannian isometry is a local Riemannian isometry. -/
@[simp]
theorem RiemannianIsometry.isLocalRiemannianIsometry (Φ : RiemannianIsometry I J M N) :
    IsLocalRiemannianIsometry I J Φ where
  contMDiff := Φ.toDiffeomorph.contMDiff
  isInvertible_mfderiv _ := Φ.toDiffeomorph.isInvertible_mfderiv (by simp)
  inner_mfderiv := Φ.inner_mfderiv

end TauCeti
