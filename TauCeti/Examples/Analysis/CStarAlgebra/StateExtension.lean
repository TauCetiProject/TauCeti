/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.Order
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
public import TauCeti.Analysis.CStarAlgebra.State.Pure

/-!
# Extensions of the state of `ℂ·1` to `M₂`

The subalgebra `ℂ·1` of a unital C⋆-algebra `A` has the unique state `c·1 ↦ c`, and every state of
`A` extends it. For `A = M_n` these examples compare two kinds of extension:

* the vector states `a ↦ ⟪ξ, a ξ⟫` of unit vectors `ξ` are pure, by
  `TauCeti.mem_extremePoints_stateSpace_of_mul_mul_eq_smul` applied to the projection `ξ ξ⋆`;
* the normalized trace of `M₂` is the midpoint of the vector states of the two standard basis
  vectors, which differ, so it is not pure.

This is the first Check of C2.1 of the CStarAlgebras roadmap.
-/

public section

noncomputable section

open Matrix CStarMatrix
open scoped ComplexOrder

namespace TauCeti.StateExtensionExamples

variable {n : Type*} [Fintype n]

/-- The matrix algebra `CStarMatrix n n ℂ` is finite-dimensional. -/
instance finiteDimensional_cstarMatrix {m : Type*} [Finite m] :
    FiniteDimensional ℂ (CStarMatrix m m ℂ) :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix m m ℂ))

/-- The vector functional `a ↦ ⟪ξ, a ξ⟫ = star ξ ⬝ᵥ (a *ᵥ ξ)` on `CStarMatrix n n ℂ`. -/
def vectorFunctional (ξ : n → ℂ) : WeakDual ℂ (CStarMatrix n n ℂ) :=
  StrongDual.toWeakDual <| LinearMap.toContinuousLinearMap
    { toFun a := star ξ ⬝ᵥ (ofMatrix.symm a *ᵥ ξ)
      map_add' a b := by
        change star ξ ⬝ᵥ ((ofMatrix.symm a + ofMatrix.symm b) *ᵥ ξ) = _
        rw [Matrix.add_mulVec, dotProduct_add]
      map_smul' c a := by
        change star ξ ⬝ᵥ ((c • ofMatrix.symm a) *ᵥ ξ) = _
        rw [Matrix.smul_mulVec, dotProduct_smul, RingHom.id_apply] }

/-- Evaluation of the vector functional. -/
theorem vectorFunctional_apply (ξ : n → ℂ) (a : CStarMatrix n n ℂ) :
    vectorFunctional ξ a = star ξ ⬝ᵥ (ofMatrix.symm a *ᵥ ξ) :=
  (rfl)

/-- The rank-one projection `ξ ξ⋆` onto the line of a unit vector `ξ`. -/
def lineProjection (ξ : n → ℂ) : CStarMatrix n n ℂ := ofMatrix (vecMulVec ξ (star ξ))

/-- The rank-one projection of a unit vector is a projection. -/
theorem isStarProjection_lineProjection {ξ : n → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1) :
    IsStarProjection (lineProjection ξ) where
  isIdempotentElem := by
    change vecMulVec ξ (star ξ) * vecMulVec ξ (star ξ) = vecMulVec ξ (star ξ)
    rw [vecMulVec_mul_vecMulVec, hξ, one_smul]
  isSelfAdjoint := by
    change (vecMulVec ξ (star ξ))ᴴ = vecMulVec ξ (star ξ)
    rw [conjTranspose_vecMulVec, star_star]

/-- The rank-one projection compresses every matrix to a multiple of itself:
`(ξ ξ⋆) a (ξ ξ⋆) = ⟪ξ, a ξ⟫ ξ ξ⋆`. -/
theorem lineProjection_mul_mul (ξ : n → ℂ) (a : CStarMatrix n n ℂ) :
    lineProjection ξ * a * lineProjection ξ = vectorFunctional ξ a • lineProjection ξ := by
  rw [vectorFunctional_apply]
  change vecMulVec ξ (star ξ) * ofMatrix.symm a * vecMulVec ξ (star ξ) =
    (star ξ ⬝ᵥ (ofMatrix.symm a *ᵥ ξ)) • vecMulVec ξ (star ξ)
  rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, ← dotProduct_mulVec, vecMulVec_smul]

/-- The vector functional of a unit vector is a state. -/
theorem vectorFunctional_mem_stateSpace {ξ : n → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1) :
    vectorFunctional ξ ∈ stateSpace (CStarMatrix n n ℂ) := by
  classical
  refine mem_stateSpace_iff_map_one.2 ⟨fun a ha ↦ ?_, ?_⟩
  · rw [vectorFunctional_apply]
    exact (nonneg_iff_posSemidef.1 ha).dotProduct_mulVec_nonneg ξ
  · rw [vectorFunctional_apply]
    change star ξ ⬝ᵥ ((1 : Matrix n n ℂ) *ᵥ ξ) = 1
    rw [one_mulVec, hξ]

/-- **Vector states are pure.** The vector state of a unit vector is an extreme point of the
state space of `M_n`. -/
theorem vectorFunctional_mem_extremePoints {ξ : n → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1) :
    vectorFunctional ξ ∈ Set.extremePoints ℝ (stateSpace (CStarMatrix n n ℂ)) := by
  classical
  refine mem_extremePoints_stateSpace_of_mul_mul_eq_smul (vectorFunctional_mem_stateSpace hξ)
    (isStarProjection_lineProjection hξ) (lineProjection_mul_mul ξ) ?_
  rw [vectorFunctional_apply]
  change star ξ ⬝ᵥ (vecMulVec ξ (star ξ) *ᵥ ξ) = 1
  rw [vecMulVec_mulVec, hξ, MulOpposite.op_one, one_smul, hξ]

/-- Every state of a unital C⋆-algebra extends the unique state `c·1 ↦ c` of `ℂ·1`. -/
theorem apply_algebraMap_of_mem_stateSpace {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] {φ : WeakDual ℂ A} (hφ : φ ∈ stateSpace A) (c : ℂ) :
    φ (algebraMap ℂ A c) = c := by
  rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one_of_mem_stateSpace hφ, smul_eq_mul,
    mul_one]

/-- The normalized trace of `M₂`, as a state. -/
def normalizedTraceState : WeakDual ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
  StrongDual.toWeakDual (normalizedTraceMap (Fin 2)).toContinuousLinearMap

/-- Evaluation of the normalized trace state. -/
theorem normalizedTraceState_apply (a : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    normalizedTraceState a = normalizedTrace a :=
  normalizedTraceMap_apply a

/-- **The normalized trace is not pure.** It is the midpoint of the vector states of the two
standard basis vectors of `ℂ²`, which differ. -/
theorem normalizedTraceState_not_mem_extremePoints :
    normalizedTraceState ∉ Set.extremePoints ℝ (stateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ)) := by
  have he (i : Fin 2) : star (Pi.single i (1 : ℂ)) ⬝ᵥ Pi.single i 1 = 1 := by simp
  intro h
  have hseg : normalizedTraceState ∈ openSegment ℝ (vectorFunctional (Pi.single 0 1))
      (vectorFunctional (Pi.single 1 1)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, DFunLike.ext _ _ fun a ↦ ?_⟩
    rw [normalizedTraceState_apply]
    change (1 / 2 : ℝ) • vectorFunctional (Pi.single 0 1) a +
      (1 / 2 : ℝ) • vectorFunctional (Pi.single 1 1) a = normalizedTrace a
    rw [vectorFunctional_apply, vectorFunctional_apply, normalizedTrace_def, Matrix.trace_fin_two]
    simp [dotProduct, mulVec, Fin.sum_univ_two, Complex.real_smul]
    ring
  have h0 := ((mem_extremePoints.1 h).2 _ (vectorFunctional_mem_stateSpace (he 0)) _
    (vectorFunctional_mem_stateSpace (he 1)) hseg).1
  have h1 : vectorFunctional (Pi.single 0 1) (ofMatrix (Matrix.single (0 : Fin 2) 0 (1 : ℂ))) =
      normalizedTraceState (ofMatrix (Matrix.single 0 0 1)) := by
    rw [h0]
  rw [vectorFunctional_apply, normalizedTraceState_apply, normalizedTrace_def,
    Matrix.trace_fin_two] at h1
  norm_num [dotProduct, mulVec, Fin.sum_univ_two] at h1

end TauCeti.StateExtensionExamples
