/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The coordinate isometry of an orthonormal family

A finite orthonormal family `v : ι → E` in an inner product space identifies Euclidean coordinate
space `EuclideanSpace 𝕜 ι` isometrically with its span: the linear-combination map

`x ↦ ∑ i, x i • v i`

preserves inner products, because `⟪∑ i, x i • v i, ∑ i, y i • v i⟫ = ∑ i, conj (x i) * y i`.
This file packages that map as the linear isometry `Orthonormal.familyIsometry`, sending the
standard basis vector `eᵢ` to `vᵢ`. No completeness, finite dimensionality, or spanning
hypothesis on `E` is needed. When the family is an orthonormal basis `b`, the coordinate isometry
is the inverse `b.repr.symm` of its coordinate map.

The adjoint of the coordinate isometry is the analysis map `y ↦ (⟪vᵢ, y⟫)ᵢ`, reading off the
coordinates of a vector against the family. Composing the adjoint of one family's coordinate
isometry with another family's gives the square matrix `(⟪uᵢ, vⱼ⟫)ᵢⱼ` of mutual inner products,
whose singular values are the cosines of the principal angles between the two spans.

## Main declarations

* `Orthonormal.familyIsometry`: the coordinate isometry `EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] E` of an
  orthonormal family.
* `Orthonormal.familyIsometry_apply`: the coordinate formula `x ↦ ∑ i, x i • v i`.
* `Orthonormal.familyIsometry_single`: the standard basis vector `eᵢ` scaled by `a` goes to
  `a • vᵢ`.
* `Orthonormal.range_familyIsometry`: the range is the span of the family.
* `Orthonormal.adjoint_familyIsometry_apply`,
  `Orthonormal.adjoint_toLinearMap_familyIsometry_apply`: the adjoint has coordinates
  `⟪vᵢ, y⟫`, for a complete and for a finite-dimensional ambient space respectively.
* `OrthonormalBasis.familyIsometry_orthonormal`: for an orthonormal basis `b`, the coordinate
  isometry is `b.repr.symm`.
-/

public section

noncomputable section

open scoped InnerProductSpace

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [Fintype ι] {v : ι → E}

namespace Orthonormal

/-- The **coordinate isometry** of a finite orthonormal family `v`: the linear isometry
`EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] E` sending the coordinate vector `x` to `∑ i, x i • v i`, and hence
the standard basis vector `eᵢ` to `vᵢ`. -/
def familyIsometry (hv : Orthonormal 𝕜 v) : EuclideanSpace 𝕜 ι →ₗᵢ[𝕜] E :=
  (Fintype.linearCombination 𝕜 v ∘ₗ (WithLp.linearEquiv 2 𝕜 (ι → 𝕜)).toLinearMap).isometryOfInner
    fun x y => by
      simp [Fintype.linearCombination_apply, hv.inner_sum, PiLp.inner_apply, mul_comm]

/-- The coordinate isometry of an orthonormal family sends `x` to `∑ i, x i • v i`. -/
theorem familyIsometry_apply (hv : Orthonormal 𝕜 v) (x : EuclideanSpace 𝕜 ι) :
    hv.familyIsometry x = ∑ i, x i • v i := by
  simp [familyIsometry, Fintype.linearCombination_apply]

/-- The coordinate isometry of an orthonormal family sends the scaled standard basis vector
`a • eᵢ` to `a • vᵢ`; in particular it sends `eᵢ` to `vᵢ`. -/
@[simp]
theorem familyIsometry_single [DecidableEq ι] (hv : Orthonormal 𝕜 v) (i : ι) (a : 𝕜) :
    hv.familyIsometry (EuclideanSpace.single i a) = a • v i := by
  simp [familyIsometry_apply, ite_smul]

/-- The range of the coordinate isometry of an orthonormal family is the span of the family. -/
theorem range_familyIsometry (hv : Orthonormal 𝕜 v) :
    LinearMap.range hv.familyIsometry.toLinearMap = Submodule.span 𝕜 (Set.range v) := by
  rw [← Fintype.range_linearCombination]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨x, by simp [familyIsometry_apply, Fintype.linearCombination_apply]⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨WithLp.toLp 2 x, by simp [familyIsometry_apply, Fintype.linearCombination_apply]⟩

/-- The adjoint of the coordinate isometry of an orthonormal family in a complete space is the
analysis map: its `i`-th coordinate at `y` is `⟪vᵢ, y⟫`. -/
@[simp]
theorem adjoint_familyIsometry_apply [CompleteSpace E] (hv : Orthonormal 𝕜 v) (y : E) (i : ι) :
    (ContinuousLinearMap.adjoint hv.familyIsometry.toContinuousLinearMap y) i = ⟪v i, y⟫_𝕜 := by
  classical
  have h := EuclideanSpace.inner_single_left i (1 : 𝕜)
    (ContinuousLinearMap.adjoint hv.familyIsometry.toContinuousLinearMap y)
  rw [map_one, one_mul, ContinuousLinearMap.adjoint_inner_right] at h
  simpa using h.symm

/-- The adjoint of the coordinate isometry of an orthonormal family in a finite-dimensional
space is the analysis map: its `i`-th coordinate at `y` is `⟪vᵢ, y⟫`. -/
@[simp]
theorem adjoint_toLinearMap_familyIsometry_apply [FiniteDimensional 𝕜 E] (hv : Orthonormal 𝕜 v)
    (y : E) (i : ι) : (LinearMap.adjoint hv.familyIsometry.toLinearMap y) i = ⟪v i, y⟫_𝕜 := by
  classical
  have h := EuclideanSpace.inner_single_left i (1 : 𝕜)
    (LinearMap.adjoint hv.familyIsometry.toLinearMap y)
  rw [map_one, one_mul, LinearMap.adjoint_inner_right] at h
  simpa using h.symm

end Orthonormal

/-- The coordinate isometry of the vectors of an orthonormal basis `b` is the inverse `b.repr.symm`
of the coordinate map of `b`. -/
@[simp]
theorem OrthonormalBasis.familyIsometry_orthonormal (b : OrthonormalBasis ι 𝕜 E) :
    b.orthonormal.familyIsometry = b.repr.symm.toLinearIsometry := by
  ext x
  simp [Orthonormal.familyIsometry_apply, OrthonormalBasis.sum_repr_symm]
