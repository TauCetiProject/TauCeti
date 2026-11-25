/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.Order
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
public import TauCeti.Analysis.CStarAlgebra.State.Pure
public import TauCeti.LinearAlgebra.Projectivization.HermitianProjector
import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Vector states of matrix algebras

For a vector `ξ : n → ℂ`, the vector functional `a ↦ ⟪ξ, a ξ⟫ = star ξ ⬝ᵥ (a *ᵥ ξ)` on the matrix
C⋆-algebra `CStarMatrix n n ℂ` is a state when `ξ` is a unit vector. It is pure: the rank-one
projection `ξ ξ⋆ = TauCeti.rankOneHermitianProjector ξ` compresses every matrix `a` to
`⟪ξ, a ξ⟫ ξ ξ⋆`, so `TauCeti.mem_extremePoints_stateSpace_of_mul_mul_eq_smul` applies. The
normalized trace, a state of `M_n` for `n` nonempty, is the average of the vector states of the
standard basis vectors.

## Main declarations

* `CStarMatrix.vectorFunctional`: the vector functional of `ξ`.
* `CStarMatrix.ofMatrix_rankOneHermitianProjector_mul_mul`: for a unit vector `ξ`, the projection
  `ξ ξ⋆` compresses `a` to `⟪ξ, a ξ⟫ ξ ξ⋆`.
* `CStarMatrix.vectorFunctional_mem_stateSpace`: the vector functional of a unit vector is a state.
* `CStarMatrix.vectorFunctional_mem_extremePoints_stateSpace`: it is a pure state.
* `CStarMatrix.normalizedTraceFunctional`: the normalized trace in the weak-* dual, a state for
  `n` nonempty (`CStarMatrix.normalizedTraceFunctional_mem_stateSpace`).
* `CStarMatrix.normalizedTraceFunctional_eq_sum_smul_vectorFunctional`: the normalized trace is
  the average of the vector states of the standard basis vectors.
-/

public section

noncomputable section

open Matrix TauCeti
open scoped ComplexOrder

namespace CStarMatrix

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

/-- The vector functional of a standard basis vector reads off a diagonal entry. -/
theorem vectorFunctional_single [DecidableEq n] (i : n) (a : CStarMatrix n n ℂ) :
    vectorFunctional (Pi.single i 1) a = a i i := by
  simp

/-- For a unit vector `ξ`, the rank-one projection `ξ ξ⋆ = rankOneHermitianProjector ξ` compresses
every matrix to a multiple of itself: `(ξ ξ⋆) a (ξ ξ⋆) = ⟪ξ, a ξ⟫ ξ ξ⋆`. -/
theorem ofMatrix_rankOneHermitianProjector_mul_mul {ξ : n → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1)
    (a : CStarMatrix n n ℂ) :
    ofMatrix (rankOneHermitianProjector ξ) * a * ofMatrix (rankOneHermitianProjector ξ) =
      vectorFunctional ξ a • ofMatrix (rankOneHermitianProjector ξ) := by
  apply ofMatrix.symm.injective
  simp [rankOneHermitianProjector_def, hξ, vecMulVec_mul, vecMul_vecMulVec,
    dotProduct_mulVec, vecMulVec_smul]

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
    ((isStarProjection_rankOneHermitianProjector ξ).map ofMatrixStarAlgEquiv)
    (ofMatrix_rankOneHermitianProjector_mul_mul hξ) ?_
  simp [← ofMatrix_eq_ofMatrixStarAlgEquiv, rankOneHermitianProjector_def, hξ, vecMulVec_mulVec]

variable (n) in
/-- The normalized trace as a functional in the weak-* dual. It is a state for a nonempty index
type, by `CStarMatrix.normalizedTraceFunctional_mem_stateSpace`. -/
def normalizedTraceFunctional : WeakDual ℂ (CStarMatrix n n ℂ) :=
  StrongDual.toWeakDual (normalizedTraceMap n).toContinuousLinearMap

/-- `normalizedTraceFunctional n` evaluates to the normalized trace. -/
@[simp]
theorem normalizedTraceFunctional_apply (x : CStarMatrix n n ℂ) :
    normalizedTraceFunctional n x = normalizedTrace x :=
  normalizedTraceMap_apply x

variable (n) in
/-- The normalized trace is a state for a nonempty index type. -/
theorem normalizedTraceFunctional_mem_stateSpace [Nonempty n] :
    normalizedTraceFunctional n ∈ stateSpace (CStarMatrix n n ℂ) :=
  (normalizedTraceMap n).toWeakDual_mem_stateSpace_iff.2 (norm_normalizedTraceMap n)

/-- The normalized trace of `M_n` is the average of the vector states of the standard basis
vectors. -/
theorem normalizedTraceFunctional_eq_sum_smul_vectorFunctional [DecidableEq n] :
    normalizedTraceFunctional n =
      ∑ i, (Fintype.card n : ℝ)⁻¹ • vectorFunctional (Pi.single i 1) := by
  refine DFunLike.ext _ _ fun a ↦ ?_
  simp [_root_.sum_apply, normalizedTrace_eq_sum, Finset.mul_sum, Complex.real_smul]

end CStarMatrix
