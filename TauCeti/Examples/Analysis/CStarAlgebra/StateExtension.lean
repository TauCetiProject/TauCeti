/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
public import TauCeti.Analysis.CStarAlgebra.Matrix.VectorState
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Extensions of the state of `ℂ·1` to `M₂`

The subalgebra `ℂ·1` of a unital C⋆-algebra `A` has the unique state `c·1 ↦ c`, and every state of
`A` extends it, by `TauCeti.map_algebraMap_of_mem_stateSpace`. For `A = M₂` these examples compare
two kinds of extension:

* the vector states `a ↦ ⟪ξ, a ξ⟫` of unit vectors `ξ` are pure, by
  `TauCeti.vectorFunctional_mem_extremePoints_stateSpace`;
* the normalized trace of `M₂` is a state, the midpoint of the vector states of the two standard
  basis vectors, which differ, so it is not pure.

So the state of `ℂ·1` has both pure and non-pure extensions to `M₂`.
-/

public section

noncomputable section

open Matrix CStarMatrix
open scoped ComplexOrder

namespace TauCeti.StateExtensionExamples

/-- The normalized trace of `M₂`, as a functional in the weak-* dual. It is a state by
`normalizedTraceState_mem_stateSpace`. -/
def normalizedTraceState : WeakDual ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) :=
  StrongDual.toWeakDual (normalizedTraceMap (Fin 2)).toContinuousLinearMap

/-- Evaluation of the normalized trace state. -/
@[simp]
theorem normalizedTraceState_apply (a : CStarMatrix (Fin 2) (Fin 2) ℂ) :
    normalizedTraceState a = normalizedTrace a :=
  normalizedTraceMap_apply a

/-- The normalized trace of `M₂` is a state. -/
theorem normalizedTraceState_mem_stateSpace :
    normalizedTraceState ∈ stateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ) := by
  refine mem_stateSpace_iff_map_one.2 ⟨fun a ha ↦ ?_, ?_⟩
  · rw [normalizedTraceState_apply]
    exact normalizedTrace_nonneg ha
  · rw [normalizedTraceState_apply, normalizedTrace_one]

/-- **The normalized trace is not pure.** The state `normalizedTraceState` (a state by
`normalizedTraceState_mem_stateSpace`) is the midpoint of the vector states of the two standard
basis vectors of `ℂ²`, which differ, so it is not an extreme point of the state space. -/
theorem normalizedTraceState_notMem_extremePoints_stateSpace :
    normalizedTraceState ∉ Set.extremePoints ℝ (stateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ)) := by
  have he (i : Fin 2) : star (Pi.single i (1 : ℂ)) ⬝ᵥ Pi.single i 1 = 1 := by simp
  intro h
  have hseg : normalizedTraceState ∈ openSegment ℝ (vectorFunctional (Pi.single 0 1))
      (vectorFunctional (Pi.single 1 1)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, DFunLike.ext _ _ fun a ↦ ?_⟩
    simp [normalizedTrace_def, Matrix.trace_fin_two, dotProduct, mulVec, Fin.sum_univ_two,
      Complex.real_smul]
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
