/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Pure
public import TauCeti.Analysis.CStarAlgebra.Matrix.VectorState
public import Mathlib.Topology.UnitInterval
import TauCeti.Examples.Analysis.CStarAlgebra.State.Extension
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Extensions of the pure state `δ₀` of `C[0,1]` to `M₂(C[0,1])`

The pure state `δ₀ : f ↦ f(0)` of `C[0,1]`, embedded in `M₂(C[0,1])` as the scalar matrices
`f ↦ diag(f, f)`, has both pure and non-pure extensions to `M₂(C[0,1])`. Evaluation at `0` is a
surjective star homomorphism `ev₀ : M₂(C[0,1]) → M₂`, and pulling back states of `M₂` along it:

* every state of `M₂` pulls back to a state extending `δ₀`;
* the vector states `f ↦ ⟪ξ, f(0) ξ⟫` of unit vectors `ξ` are pure, since the
  pullback of a pure state along a surjective star homomorphism is pure
  (`TauCeti.pullbackFunctional_mem_extremePoints_stateSpace`);
* the state `f ↦ tr(f(0))/2` is not pure, since the normalized trace of `M₂` is not pure and
  purity is detected by pullback along `ev₀`
  (`TauCeti.pullbackFunctional_mem_extremePoints_stateSpace_iff`).
-/

public section

noncomputable section

open CStarMatrix
open scoped ComplexOrder

namespace TauCeti.PureExtensionExamples

/-- Evaluation at `0` entrywise, `M₂(C[0,1]) → M₂`. -/
abbrev ev₀ : CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ) →⋆ₙₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) ℂ :=
  mapₙₐ (ContinuousMap.evalStarAlgHom ℂ ℂ (0 : unitInterval)).toNonUnitalStarAlgHom

/-- Evaluation at `0` is surjective: constant matrices are preimages. -/
theorem ev₀_surjective : Function.Surjective ev₀ := fun M ↦
  ⟨M.map (ContinuousMap.const unitInterval), by ext i j; rfl⟩

/-- Evaluation at `0` sends the scalar matrix of `f` to the scalar matrix of `f(0)`. -/
theorem ev₀_algebraMap (f : C(unitInterval, ℂ)) :
    ev₀ (algebraMap C(unitInterval, ℂ) (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ)) f) =
      algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ) (f 0) := by
  ext i j
  by_cases h : i = j <;> simp [CStarMatrix.algebraMap_apply, h]

/-- **Every state of `M₂` pulls back to an extension of `δ₀`.** The pullback along `ev₀` of a
state `χ` of `M₂` sends the scalar matrix of `f` to `f(0)`. -/
theorem pullbackFunctional_ev₀_apply_algebraMap {χ : WeakDual ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ)}
    (hχ : χ ∈ stateSpace (CStarMatrix (Fin 2) (Fin 2) ℂ)) (f : C(unitInterval, ℂ)) :
    pullbackFunctional _ ev₀ χ (algebraMap _ (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ)) f) =
      f 0 := by
  rw [pullbackFunctional_apply, ev₀_algebraMap, map_algebraMap_of_mem_stateSpace hχ]

/-- **Pure extensions of `δ₀`.** For a unit vector `ξ`, the state `f ↦ ⟪ξ, f(0) ξ⟫` of
`M₂(C[0,1])` is pure; it extends `δ₀` by `pullbackFunctional_ev₀_apply_algebraMap`. -/
theorem pullbackFunctional_vectorFunctional_mem_extremePoints_stateSpace {ξ : Fin 2 → ℂ}
    (hξ : star ξ ⬝ᵥ ξ = 1) :
    pullbackFunctional _ ev₀ (vectorFunctional ξ) ∈
      Set.extremePoints ℝ (stateSpace (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ))) :=
  pullbackFunctional_mem_extremePoints_stateSpace ev₀ ev₀_surjective
    (vectorFunctional_mem_extremePoints_stateSpace hξ)

/-- The functional `f ↦ tr(f(0))/2` of `M₂(C[0,1])` is a state; it extends `δ₀` by
`pullbackFunctional_ev₀_apply_algebraMap`. -/
theorem pullbackFunctional_normalizedTraceFunctional_mem_stateSpace :
    pullbackFunctional _ ev₀ (normalizedTraceFunctional (Fin 2)) ∈
      stateSpace (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ)) :=
  mapsTo_pullbackFunctional_stateSpace_of_surjective ev₀ ev₀_surjective
    (normalizedTraceFunctional_mem_stateSpace (Fin 2))

/-- **A non-pure extension of `δ₀`.** The state `f ↦ tr(f(0))/2` of `M₂(C[0,1])` is not pure. -/
theorem pullbackFunctional_normalizedTraceFunctional_notMem_extremePoints_stateSpace :
    pullbackFunctional _ ev₀ (normalizedTraceFunctional (Fin 2)) ∉
      Set.extremePoints ℝ (stateSpace (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ))) := by
  rw [pullbackFunctional_mem_extremePoints_stateSpace_iff ev₀ ev₀_surjective]
  exact StateExtensionExamples.normalizedTraceFunctional_notMem_extremePoints_stateSpace

end TauCeti.PureExtensionExamples
