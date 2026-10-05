/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Affine.MazurUlam
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Distance
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Action

/-!
# The isometry group of Euclidean space

A real inner product space `F` is a Riemannian manifold for the flat metric given by the inner
product on each tangent space, and its Riemannian distance is the norm distance. This file
identifies its Riemannian isometries with its affine isometries:

* an affine isometry `F ≃ᵃⁱ[ℝ] G` is smooth, and its differential at every point is its linear
  part, which preserves inner products, so it is a Riemannian isometry;
* conversely, a Riemannian isometry preserves the Riemannian distance, which is the norm
  distance, so it is affine by the Mazur–Ulam theorem
  (`IsometryEquiv.toRealAffineIsometryEquiv`).

For self-maps this is an isomorphism between the Riemannian isometry group `Isom 𝓘(ℝ, F) F` and
the affine isometry group `F ≃ᵃⁱ[ℝ] F` of rigid motions. Translations act transitively, so
Euclidean space is a homogeneous Riemannian manifold, and the isotropy group of the origin is the
orthogonal group `F ≃ₗᵢ[ℝ] F`. With `F = EuclideanSpace ℝ (Fin 3)` this is the Euclidean model
geometry `(𝔼³, Isom(𝔼³))`, one of Thurston's eight three-dimensional geometries.

## Main definitions

* `AffineIsometryEquiv.toRiemannianIsometry`: an affine isometry as a Riemannian isometry.
* `TauCeti.RiemannianIsometry.toAffineIsometryEquiv`: a Riemannian isometry of real inner product
  spaces as an affine isometry.
* `TauCeti.RiemannianIsometry.affineIsometryMulEquiv`: the isomorphism between the Riemannian
  isometry group of a real inner product space and its affine isometry group.
* `TauCeti.RiemannianIsometry.stabilizerZeroMulEquiv`: the isomorphism between the isotropy group
  of the origin and the linear isometry group.

## Main results

* `TauCeti.RiemannianIsometry.isPretransitive_innerProductSpace`: the isometry group of a real
  inner product space acts transitively on it.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176, Chapters 2 and 3
  (homogeneous Riemannian manifolds, and Euclidean space with its group of rigid motions).
* W. P. Thurston, *Three-Dimensional Geometry and Topology, Vol. 1*, Princeton (1997), §3.8
  (the eight model geometries).
-/

public section

open Bundle Manifold
open scoped ContDiff Manifold

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G]

namespace AffineIsometryEquiv

/-- An affine isometry between real inner product spaces is a smooth Riemannian isometry for their
flat metrics: its differential at every point is its linear part, a linear isometry. -/
def toRiemannianIsometry (f : F ≃ᵃⁱ[ℝ] G) :
    TauCeti.RiemannianIsometry 𝓘(ℝ, F) 𝓘(ℝ, G) F G where
  toEquiv := f.toEquiv
  contMDiff_toFun := f.toAffineIsometry.toContinuousAffineMap.contDiff.contMDiff
  contMDiff_invFun := f.symm.toAffineIsometry.toContinuousAffineMap.contDiff.contMDiff
  inner_mfderiv' x v w := by
    have hf : HasFDerivAt f (f.linearIsometryEquiv.toContinuousLinearEquiv : F →L[ℝ] G) x := by
      convert f.toAffineIsometry.toContinuousAffineMap.hasFDerivAt (x := x) using 1
      · ext u
        simp
      · ext u
        simpa using (f.map_vsub u 0).trans
          (f.toAffineIsometry.toContinuousAffineMap.contLinear_map_vsub u 0).symm
    have h : mfderiv 𝓘(ℝ, F) 𝓘(ℝ, G) f x =
        (f.linearIsometryEquiv.toContinuousLinearEquiv : F →L[ℝ] G) :=
      hf.hasMFDerivAt.mfderiv
    exact (congrArg₂ (inner ℝ) (DFunLike.congr_fun h v) (DFunLike.congr_fun h w)).trans
      (f.linearIsometryEquiv.inner_map_map v w)

/-- The Riemannian isometry of an affine isometry has the same underlying function. -/
@[simp]
theorem coe_toRiemannianIsometry (f : F ≃ᵃⁱ[ℝ] G) : ⇑f.toRiemannianIsometry = f := (rfl)

end AffineIsometryEquiv

namespace TauCeti.RiemannianIsometry

/-- A Riemannian isometry between real inner product spaces is an affine isometry: it preserves
the Riemannian distance, which is the norm distance, so it is affine by the Mazur–Ulam theorem. -/
def toAffineIsometryEquiv (Φ : RiemannianIsometry 𝓘(ℝ, F) 𝓘(ℝ, G) F G) : F ≃ᵃⁱ[ℝ] G :=
  (Φ : F ≃ᵢ G).toRealAffineIsometryEquiv

/-- The affine isometry of a Riemannian isometry has the same underlying function. -/
@[simp]
theorem coe_toAffineIsometryEquiv (Φ : RiemannianIsometry 𝓘(ℝ, F) 𝓘(ℝ, G) F G) :
    ⇑Φ.toAffineIsometryEquiv = Φ := by
  simp [toAffineIsometryEquiv]

/-- Viewing an affine isometry as a Riemannian isometry and back gives the original map. -/
@[simp]
theorem toAffineIsometryEquiv_toRiemannianIsometry (f : F ≃ᵃⁱ[ℝ] G) :
    f.toRiemannianIsometry.toAffineIsometryEquiv = f := by
  ext x
  simp

/-- A Riemannian isometry of real inner product spaces is determined by its affine isometry. -/
@[simp]
theorem toRiemannianIsometry_toAffineIsometryEquiv
    (Φ : RiemannianIsometry 𝓘(ℝ, F) 𝓘(ℝ, G) F G) :
    Φ.toAffineIsometryEquiv.toRiemannianIsometry = Φ := by
  ext x
  simp

/-- The Riemannian isometry group of a real inner product space is its affine isometry group, the
group of rigid motions. -/
def affineIsometryMulEquiv : Isom 𝓘(ℝ, F) F ≃* (F ≃ᵃⁱ[ℝ] F) where
  toFun := toAffineIsometryEquiv
  invFun := AffineIsometryEquiv.toRiemannianIsometry
  left_inv := toRiemannianIsometry_toAffineIsometryEquiv
  right_inv := toAffineIsometryEquiv_toRiemannianIsometry
  map_mul' Φ Ψ := by
    ext x
    simp

/-- The isomorphism of isometry groups sends a Riemannian isometry to its affine isometry. -/
@[simp]
theorem affineIsometryMulEquiv_apply (Φ : Isom 𝓘(ℝ, F) F) :
    affineIsometryMulEquiv Φ = Φ.toAffineIsometryEquiv := (rfl)

/-- The inverse isomorphism of isometry groups views an affine isometry as a Riemannian one. -/
@[simp]
theorem affineIsometryMulEquiv_symm_apply (f : F ≃ᵃⁱ[ℝ] F) :
    affineIsometryMulEquiv.symm f = f.toRiemannianIsometry := (rfl)

/-- The isotropy group of the origin in the isometry group of a real inner product space is its
linear isometry group, the orthogonal group `O(F)`: an isometry fixing the origin is linear by the
Mazur–Ulam theorem. -/
def stabilizerZeroMulEquiv :
    MulAction.stabilizer (Isom 𝓘(ℝ, F) F) (0 : F) ≃* (F ≃ₗᵢ[ℝ] F) where
  toFun Φ := (Φ.1 : F ≃ᵢ F).toRealLinearIsometryEquivOfMapZero
    (by simpa using MulAction.mem_stabilizer_iff.mp Φ.2)
  invFun L := ⟨L.toAffineIsometryEquiv.toRiemannianIsometry, by simp⟩
  left_inv Φ := by
    ext x
    simp
  right_inv L := by
    ext x
    simp
  map_mul' Φ Ψ := by
    ext x
    simp

/-- The linear isometry of an isometry fixing the origin has the same underlying function. -/
@[simp]
theorem coe_stabilizerZeroMulEquiv
    (Φ : MulAction.stabilizer (Isom 𝓘(ℝ, F) F) (0 : F)) :
    ⇑(stabilizerZeroMulEquiv Φ) = Φ.1 := by
  simp [stabilizerZeroMulEquiv]

/-- A linear isometry, viewed as an isometry fixing the origin, has the same underlying function.
-/
@[simp]
theorem coe_stabilizerZeroMulEquiv_symm (L : F ≃ₗᵢ[ℝ] F) :
    ⇑(stabilizerZeroMulEquiv.symm L).1 = L := by
  simp [stabilizerZeroMulEquiv]

/-- Euclidean space is a homogeneous Riemannian manifold: translations are isometries, so the
isometry group of a real inner product space acts transitively on it. -/
instance isPretransitive_innerProductSpace :
    MulAction.IsPretransitive (Isom 𝓘(ℝ, F) F) F where
  exists_smul_eq x y :=
    ⟨(AffineIsometryEquiv.constVAdd ℝ F (y - x)).toRiemannianIsometry, by simp⟩

end TauCeti.RiemannianIsometry

end
