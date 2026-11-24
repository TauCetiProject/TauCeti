/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap
public import Mathlib.Topology.Instances.Matrix

/-!
# Matrices as continuous linear maps of coordinate spaces

Over a topological commutative ring `R`, an invertible square matrix `g` acts on `ι → R` by
`Matrix.mulVec` as a continuous linear automorphism
(`Matrix.GeneralLinearGroup.toContinuousLinearEquiv`). This is `Matrix.GeneralLinearGroup.toLin`
with the continuity of `Matrix.mulVec`, bundled as a monoid hom into the automorphism group
`ContinuousLinearEquiv.automorphismGroup`: products of matrices act by composition, the first factor
acting last, and inverses act by the inverse automorphism. This is how the general linear group
acts on frames `𝕜ⁿ ≃ V` by precomposition.

Over a complete nontrivially normed field `𝕜`, an isomorphism `σ : F ≃ 𝕜ⁿ` identifies the continuous
linear maps `𝕜ⁿ →L[𝕜] F` with the square matrices, sending `φ` to the matrix of `σ ∘ φ`
(`ContinuousLinearEquiv.toMatrixCLE`).
-/

public section

noncomputable section

open scoped Matrix

namespace Matrix.GeneralLinearGroup

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [TopologicalSpace R]
  [IsTopologicalRing R]

/-- The continuous linear automorphism of `ι → R` given by an invertible matrix, acting by
`Matrix.mulVec`. As a monoid hom into the automorphism group, a product `g * h` acts by applying `h`
first and then `g`. -/
def toContinuousLinearEquiv : GL ι R →* ((ι → R) ≃L[R] (ι → R)) where
  toFun g :=
    { toLinearEquiv := (toLin g).toLinearEquiv
      continuous_toFun := continuous_const.matrix_mulVec continuous_id
      continuous_invFun := continuous_const.matrix_mulVec continuous_id }
  map_one' := ContinuousLinearEquiv.ext <| funext Matrix.one_mulVec
  map_mul' g h := ContinuousLinearEquiv.ext <| funext fun w ↦
    (Matrix.mulVec_mulVec w (g : Matrix ι ι R) h).symm

@[simp]
theorem toContinuousLinearEquiv_apply (g : GL ι R) (w : ι → R) :
    toContinuousLinearEquiv g w = (g : Matrix ι ι R) *ᵥ w :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_symm_apply (g : GL ι R) (w : ι → R) :
    (toContinuousLinearEquiv g).symm w = ((g⁻¹ : GL ι R) : Matrix ι ι R) *ᵥ w :=
  (rfl)

end Matrix.GeneralLinearGroup

namespace ContinuousLinearEquiv

variable {ι 𝕜 F : Type*} [Fintype ι] [DecidableEq ι] [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- For `σ : F ≃ 𝕜ⁿ`, the matrix of `σ ∘ φ`, for `φ : 𝕜ⁿ →L[𝕜] F`, as a continuous linear
isomorphism. Its inverse sends a matrix `M` to `w ↦ σ⁻¹ (M *ᵥ w)`. -/
def toMatrixCLE (σ : F ≃L[𝕜] (ι → 𝕜)) : ((ι → 𝕜) →L[𝕜] F) ≃L[𝕜] Matrix ι ι 𝕜 :=
  ((ContinuousLinearEquiv.refl 𝕜 (ι → 𝕜)).arrowCongr σ).trans
    (LinearMap.toContinuousLinearMap.symm.trans LinearMap.toMatrix').toContinuousLinearEquiv

theorem toMatrixCLE_apply (σ : F ≃L[𝕜] (ι → 𝕜)) (φ : (ι → 𝕜) →L[𝕜] F) :
    σ.toMatrixCLE φ = LinearMap.toMatrix' ((σ : F →L[𝕜] (ι → 𝕜)) ∘L φ) :=
  (rfl)

@[simp]
theorem toMatrixCLE_symm_apply (σ : F ≃L[𝕜] (ι → 𝕜)) (M : Matrix ι ι 𝕜) (w : ι → 𝕜) :
    σ.toMatrixCLE.symm M w = σ.symm (M *ᵥ w) := by
  simp [toMatrixCLE, ContinuousLinearEquiv.arrowCongr_symm, Matrix.toLin'_apply]

/-- The matrix of `σ ∘ φ` acts on `𝕜ⁿ` as `σ ∘ φ`. -/
@[simp]
theorem toMatrixCLE_mulVec (σ : F ≃L[𝕜] (ι → 𝕜)) (φ : (ι → 𝕜) →L[𝕜] F) (w : ι → 𝕜) :
    σ.toMatrixCLE φ *ᵥ w = σ (φ w) := by
  simp [toMatrixCLE_apply, LinearMap.toMatrix'_mulVec]

/-- Precomposing with the action of an invertible matrix multiplies the matrix on the right. -/
theorem toMatrixCLE_comp_toContinuousLinearEquiv (σ : F ≃L[𝕜] (ι → 𝕜))
    (φ : (ι → 𝕜) →L[𝕜] F) (g : GL ι 𝕜) :
    σ.toMatrixCLE (φ ∘L (Matrix.GeneralLinearGroup.toContinuousLinearEquiv g :
      (ι → 𝕜) →L[𝕜] (ι → 𝕜))) = σ.toMatrixCLE φ * (g : Matrix ι ι 𝕜) := by
  refine σ.toMatrixCLE.symm.injective <| ContinuousLinearMap.ext fun w ↦ ?_
  simp [← Matrix.mulVec_mulVec]

/-- The inverse of `σ` has the identity matrix. -/
@[simp]
theorem toMatrixCLE_symm_self (σ : F ≃L[𝕜] (ι → 𝕜)) :
    σ.toMatrixCLE (σ.symm : (ι → 𝕜) →L[𝕜] F) = 1 := by
  refine σ.toMatrixCLE.symm.injective <| ContinuousLinearMap.ext fun w ↦ ?_
  simp

end ContinuousLinearEquiv
