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
with the continuity of `Matrix.mulVec`. Products of matrices act by composition, the first factor
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
`Matrix.mulVec`. -/
def toContinuousLinearEquiv (g : GL ι R) : (ι → R) ≃L[R] (ι → R) where
  toLinearEquiv := (toLin g).toLinearEquiv
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

@[simp]
theorem toContinuousLinearEquiv_apply (g : GL ι R) (w : ι → R) :
    g.toContinuousLinearEquiv w = (g : Matrix ι ι R) *ᵥ w :=
  (rfl)

@[simp]
theorem toContinuousLinearEquiv_one :
    (1 : GL ι R).toContinuousLinearEquiv = ContinuousLinearEquiv.refl R (ι → R) :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ by simp

/-- The product `g * h` acts by applying `h` first and then `g`. -/
@[simp]
theorem toContinuousLinearEquiv_mul (g h : GL ι R) :
    (g * h).toContinuousLinearEquiv = h.toContinuousLinearEquiv.trans g.toContinuousLinearEquiv :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ by simp [Matrix.mulVec_mulVec]

@[simp]
theorem toContinuousLinearEquiv_inv (g : GL ι R) :
    g⁻¹.toContinuousLinearEquiv = g.toContinuousLinearEquiv.symm :=
  ContinuousLinearEquiv.ext <| funext fun w ↦ by
    simp [ContinuousLinearEquiv.eq_symm_apply, Matrix.mulVec_mulVec]

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

end ContinuousLinearEquiv
