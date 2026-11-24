/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.Order
public import TauCeti.Analysis.CStarAlgebra.State.Pure
import TauCeti.Analysis.CStarAlgebra.CStarMatrix

/-!
# Vector states of matrix algebras

For a vector `ξ : n → ℂ`, the vector functional `a ↦ ⟪ξ, a ξ⟫ = star ξ ⬝ᵥ (a *ᵥ ξ)` on the matrix
C⋆-algebra `CStarMatrix n n ℂ` is a state when `ξ` is a unit vector. It is pure: the rank-one
projection `ξ ξ⋆` compresses every matrix `a` to `⟪ξ, a ξ⟫ ξ ξ⋆`, so
`TauCeti.mem_extremePoints_stateSpace_of_mul_mul_eq_smul` applies.

## Main declarations

* `TauCeti.vectorFunctional`: the vector functional of `ξ`.
* `TauCeti.vecMulVecStar`: the rank-one matrix `ξ ξ⋆`, the projection onto the line of `ξ` for
  a unit vector `ξ` (`TauCeti.isStarProjection_vecMulVecStar`).
* `TauCeti.vectorFunctional_mem_stateSpace`: the vector functional of a unit vector is a state.
* `TauCeti.vectorFunctional_mem_extremePoints_stateSpace`: it is a pure state.
-/

public section

noncomputable section

open Matrix CStarMatrix
open scoped ComplexOrder

namespace TauCeti

variable {n : Type*} [Fintype n]

/-- The vector functional `a ↦ ⟪ξ, a ξ⟫ = star ξ ⬝ᵥ (a *ᵥ ξ)` on `CStarMatrix n n ℂ`. -/
def vectorFunctional (ξ : n → ℂ) : WeakDual ℂ (CStarMatrix n n ℂ) :=
  StrongDual.toWeakDual <| LinearMap.toContinuousLinearMap
    { toFun a := star ξ ⬝ᵥ (ofMatrix.symm a *ᵥ ξ)
      map_add' a b := by rw [ofMatrix_symm_add, Matrix.add_mulVec, dotProduct_add]
      map_smul' c a := by
        rw [ofMatrix_symm_smul, Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply] }

/-- Evaluation of the vector functional. -/
@[simp]
theorem vectorFunctional_apply (ξ : n → ℂ) (a : CStarMatrix n n ℂ) :
    vectorFunctional ξ a = star ξ ⬝ᵥ (ofMatrix.symm a *ᵥ ξ) :=
  (rfl)

/-- The rank-one matrix `ξ ξ⋆ = vecMulVec ξ (star ξ)`. For a unit vector `ξ` it is the projection
onto the line of `ξ`, by `TauCeti.isStarProjection_vecMulVecStar`. -/
def vecMulVecStar {m : Type*} (ξ : m → ℂ) : CStarMatrix m m ℂ := ofMatrix (vecMulVec ξ (star ξ))

/-- The rank-one matrix `ξ ξ⋆`, read as an ordinary matrix. -/
@[simp]
theorem ofMatrix_symm_vecMulVecStar {m : Type*} (ξ : m → ℂ) :
    ofMatrix.symm (vecMulVecStar ξ) = vecMulVec ξ (star ξ) :=
  (rfl)

/-- For a unit vector `ξ`, the rank-one matrix `ξ ξ⋆` is a projection. -/
theorem isStarProjection_vecMulVecStar {ξ : n → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1) :
    IsStarProjection (vecMulVecStar ξ) where
  isIdempotentElem := ofMatrix.symm.injective <| by
    rw [ofMatrix_symm_mul, ofMatrix_symm_vecMulVecStar, vecMulVec_mul_vecMulVec, hξ, one_smul]
  isSelfAdjoint := ofMatrix.symm.injective <| by
    rw [ofMatrix_symm_star, ofMatrix_symm_vecMulVecStar, conjTranspose_vecMulVec, star_star]

/-- The rank-one matrix `ξ ξ⋆` compresses every matrix to a multiple of itself:
`(ξ ξ⋆) a (ξ ξ⋆) = ⟪ξ, a ξ⟫ ξ ξ⋆`. -/
theorem vecMulVecStar_mul_mul (ξ : n → ℂ) (a : CStarMatrix n n ℂ) :
    vecMulVecStar ξ * a * vecMulVecStar ξ = vectorFunctional ξ a • vecMulVecStar ξ := by
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_mul, ofMatrix_symm_smul, ofMatrix_symm_vecMulVecStar,
    vectorFunctional_apply]
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, vecMulVec_smul]

/-- The vector functional of a unit vector is a state. -/
theorem vectorFunctional_mem_stateSpace {ξ : n → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1) :
    vectorFunctional ξ ∈ stateSpace (CStarMatrix n n ℂ) := by
  classical
  refine mem_stateSpace_iff_map_one.2 ⟨fun a ha ↦ ?_, ?_⟩
  · rw [vectorFunctional_apply]
    exact (nonneg_iff_posSemidef.1 ha).dotProduct_mulVec_nonneg ξ
  · rw [vectorFunctional_apply, ofMatrix_symm_one, one_mulVec, hξ]

/-- **Vector states are pure.** The vector state of a unit vector is an extreme point of the
state space of `M_n`. -/
theorem vectorFunctional_mem_extremePoints_stateSpace {ξ : n → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1) :
    vectorFunctional ξ ∈ Set.extremePoints ℝ (stateSpace (CStarMatrix n n ℂ)) := by
  classical
  refine mem_extremePoints_stateSpace_of_mul_mul_eq_smul (vectorFunctional_mem_stateSpace hξ)
    (isStarProjection_vecMulVecStar hξ) (vecMulVecStar_mul_mul ξ) ?_
  rw [vectorFunctional_apply, ofMatrix_symm_vecMulVecStar, vecMulVec_mulVec, hξ,
    MulOpposite.op_one, one_smul, hξ]

end TauCeti
