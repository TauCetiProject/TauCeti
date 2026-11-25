/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.State.Pure
public import TauCeti.Analysis.CStarAlgebra.Matrix.VectorState
public import Mathlib.Topology.UnitInterval
import TauCeti.Examples.Analysis.CStarAlgebra.StateExtension
import TauCeti.Topology.Algebra.Module.Spaces.WeakDual

/-!
# Extensions of the pure state `δ₀` of `C[0,1]` to `M₂(C[0,1])`

The pure state `δ₀ : f ↦ f(0)` of `C[0,1]`, embedded in `M₂(C[0,1])` as the scalar matrices
`f ↦ diag(f, f)`, has both pure and non-pure extensions to `M₂(C[0,1])`. Evaluation at `0` is a
surjective star homomorphism `ev₀ : M₂(C[0,1]) → M₂`, and pulling back states of `M₂` along it:

* the vector states `f ↦ ⟪ξ, f(0) ξ⟫` of unit vectors `ξ` extend `δ₀` and are pure, since the
  pullback of a pure state along a surjective star homomorphism is pure
  (`TauCeti.pullbackFunctional_mem_extremePoints_stateSpace`);
* the state `f ↦ tr(f(0))/2` extends `δ₀` and is not pure, as the midpoint of the pullbacks of
  the vector states of the two standard basis vectors.
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
  change (if i = j then f else 0) 0 = if i = j then f 0 else 0
  split_ifs <;> rfl

/-- **Pure extensions of `δ₀`.** For a unit vector `ξ`, the state `f ↦ ⟪ξ, f(0) ξ⟫` of
`M₂(C[0,1])` is pure and extends `δ₀` on the scalar matrices. -/
theorem pure_extension {ξ : Fin 2 → ℂ} (hξ : star ξ ⬝ᵥ ξ = 1) :
    pullbackFunctional _ ev₀ (vectorFunctional ξ) ∈
        Set.extremePoints ℝ (stateSpace (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ))) ∧
      ∀ f : C(unitInterval, ℂ), pullbackFunctional _ ev₀ (vectorFunctional ξ)
        (algebraMap _ (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ)) f) = f 0 := by
  refine ⟨pullbackFunctional_mem_extremePoints_stateSpace ev₀ ev₀_surjective
    (vectorFunctional_mem_extremePoints_stateSpace hξ), fun f ↦ ?_⟩
  rw [pullbackFunctional_apply, ev₀_algebraMap,
    map_algebraMap_of_mem_stateSpace (vectorFunctional_mem_stateSpace hξ)]

/-- **A non-pure extension of `δ₀`.** The state `f ↦ tr(f(0))/2` of `M₂(C[0,1])` extends `δ₀` on
the scalar matrices but is not pure. -/
theorem trace_extension :
    pullbackFunctional _ ev₀ (normalizedTraceFunctional (Fin 2)) ∉
        Set.extremePoints ℝ (stateSpace (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ))) ∧
      ∀ f : C(unitInterval, ℂ), pullbackFunctional _ ev₀ (normalizedTraceFunctional (Fin 2))
        (algebraMap _ (CStarMatrix (Fin 2) (Fin 2) C(unitInterval, ℂ)) f) = f 0 := by
  have he (i : Fin 2) : star (Pi.single i (1 : ℂ)) ⬝ᵥ Pi.single i 1 = 1 := by simp
  have hinj : Function.Injective (pullbackFunctional _ ev₀) := fun χ χ' h ↦
    DFunLike.ext _ _ fun b ↦ by
      obtain ⟨a, rfl⟩ := ev₀_surjective b
      simpa using congrArg (fun χ'' : WeakDual ℂ _ ↦ χ'' a) h
  refine ⟨fun h ↦ ?_, fun f ↦ ?_⟩
  · have hseg : pullbackFunctional _ ev₀ (normalizedTraceFunctional (Fin 2)) ∈ openSegment ℝ
        (pullbackFunctional _ ev₀ (vectorFunctional (Pi.single 0 1)))
        (pullbackFunctional _ ev₀ (vectorFunctional (Pi.single 1 1))) :=
      ⟨2⁻¹, 2⁻¹, by norm_num, by norm_num, by norm_num, by
        rw [normalizedTraceFunctional_eq_sum_smul_vectorFunctional, Fin.sum_univ_two]
        have hsm (r : ℝ) (χ : WeakDual ℂ (CStarMatrix (Fin 2) (Fin 2) ℂ)) :
            pullbackFunctional _ ev₀ (r • χ) = r • pullbackFunctional _ ev₀ χ :=
          DFunLike.ext _ _ fun _ ↦ by simp [pullbackFunctional_apply]
        simp only [map_add, hsm, Fintype.card_fin]
        norm_num⟩
    have h0 := hinj ((mem_extremePoints.1 h).2 _
      (mapsTo_pullbackFunctional_stateSpace_of_surjective ev₀ ev₀_surjective
        (vectorFunctional_mem_stateSpace (he 0))) _
      (mapsTo_pullbackFunctional_stateSpace_of_surjective ev₀ ev₀_surjective
        (vectorFunctional_mem_stateSpace (he 1))) hseg).1
    exact StateExtensionExamples.normalizedTraceFunctional_notMem_extremePoints_stateSpace
      (h0 ▸ vectorFunctional_mem_extremePoints_stateSpace (he 0))
  · rw [pullbackFunctional_apply, ev₀_algebraMap,
      map_algebraMap_of_mem_stateSpace (normalizedTraceFunctional_mem_stateSpace (Fin 2))]

end TauCeti.PureExtensionExamples
