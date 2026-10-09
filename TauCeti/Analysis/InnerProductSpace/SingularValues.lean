/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues

/-!
# Singular values and the eigenbasis of the Gram operator

For a linear map `A : E → F` between finite-dimensional inner product spaces, Mathlib's
`LinearMap.singularValues` are the square roots of the eigenvalues of the Gram operator `A† A`,
listed in the order of its ordered orthonormal eigenbasis
`(vᵢ) = A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl` (`LinearMap.sq_singularValues_fin`).
This file records how `A` acts on that basis, the right singular vectors of `A`:

* `LinearMap.adjoint_comp_self_eigenvectorBasis`: `A† A vᵢ = σᵢ² vᵢ`;
* `LinearMap.inner_apply_eigenvectorBasis`: `⟪A vᵢ, A x⟫ = σᵢ² ⟪vᵢ, x⟫`;
* `LinearMap.inv_mul_smul_apply_eigenvectorBasis`: `(σᵢ⁻² σᵢ²) A vᵢ = A vᵢ`, which holds also
  when `σᵢ = 0` because `vᵢ` then lies in the kernel of `A`.
-/

public section

open Module InnerProductSpace

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F] (A : E →ₗ[𝕜] F)

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The right singular vectors are eigenvectors of `A† A` for the squared singular values. -/
theorem adjoint_comp_self_eigenvectorBasis (i : Fin (finrank 𝕜 E)) :
    (A.adjoint ∘ₗ A) (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i) =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) •
        A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i := by
  rw [A.sq_singularValues_fin rfl]
  exact A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i

/-- Inner products of `A vᵢ` against the range of `A`: `⟪A vᵢ, A x⟫ = σᵢ² ⟪vᵢ, x⟫` for a right
singular vector `vᵢ`. -/
theorem inner_apply_eigenvectorBasis (i : Fin (finrank 𝕜 E)) (x : E) :
    ⟪A (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i), A x⟫ =
      ((A.singularValues i ^ 2 : ℝ) : 𝕜) *
        ⟪A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i, x⟫ := by
  rw [← adjoint_inner_left, ← comp_apply, adjoint_comp_self_eigenvectorBasis, inner_smul_left,
    RCLike.conj_ofReal]

/-- A right singular vector with singular value zero lies in the kernel, so `A vᵢ` is fixed by
the scalar `σᵢ⁻² σᵢ²` (with total field inversion) even when `σᵢ = 0`. -/
theorem inv_mul_smul_apply_eigenvectorBasis (i : Fin (finrank 𝕜 E)) :
    (((A.singularValues i ^ 2 : ℝ) : 𝕜)⁻¹ * ((A.singularValues i ^ 2 : ℝ) : 𝕜)) •
      A (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i) =
      A (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i) := by
  by_cases hc : ((A.singularValues i ^ 2 : ℝ) : 𝕜) = 0
  · have h : A (A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i) = 0 := by
      rw [← inner_self_eq_zero (𝕜 := 𝕜), inner_apply_eigenvectorBasis, hc, zero_mul]
    rw [h, smul_zero]
  · rw [inv_mul_cancel₀ hc, one_smul]

end LinearMap
