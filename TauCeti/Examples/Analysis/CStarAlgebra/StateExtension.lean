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
  `CStarMatrix.vectorFunctional_mem_extremePoints_stateSpace`;
* the normalized trace of `M₂`, a state by
  `CStarMatrix.normalizedTraceFunctional_mem_stateSpace`, is the midpoint of the vector states of
  the two standard basis vectors, which differ, so it is not pure.

So the state of `ℂ·1` has both pure and non-pure extensions to `M₂`.
-/

public section

noncomputable section

open Matrix CStarMatrix
open scoped ComplexOrder

namespace TauCeti.StateExtensionExamples

/-- **The normalized trace is not pure.** The state `normalizedTraceFunctional (Fin 2)` (a state
by `CStarMatrix.normalizedTraceFunctional_mem_stateSpace`) is the midpoint of the vector states of
the two standard basis vectors of `ℂ²`, which differ, so it is not an extreme point of the state
space. -/
theorem normalizedTraceFunctional_notMem_extremePoints_stateSpace :
    normalizedTraceFunctional (Fin 2) ∉
      Set.extremePoints ℝ (stateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ)) := by
  have he (i : Fin 2) : star (Pi.single i (1 : ℂ)) ⬝ᵥ Pi.single i 1 = 1 := by simp
  intro h
  have hseg : normalizedTraceFunctional (Fin 2) ∈
      openSegment ℝ (vectorFunctional (Pi.single 0 1)) (vectorFunctional (Pi.single 1 1)) :=
    ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num,
      by simp [normalizedTraceFunctional_eq_sum_smul_vectorFunctional, Fin.sum_univ_two]⟩
  have h0 := ((mem_extremePoints.1 h).2 _ (vectorFunctional_mem_stateSpace (he 0)) _
    (vectorFunctional_mem_stateSpace (he 1)) hseg).1
  have h1 := DFunLike.congr_fun h0 (ofMatrix (Matrix.single (0 : Fin 2) 0 (1 : ℂ)))
  rw [vectorFunctional_single, normalizedTraceFunctional_apply, normalizedTrace_eq_sum] at h1
  norm_num [Fin.sum_univ_two] at h1

end TauCeti.StateExtensionExamples
