/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Analysis.Normed.Module.Alternating.Wedge.ContinuousLinearMap

/-!
# Paired wedges in alternating-bundle trivializations

Fibrewise paired wedges commute with passing into bundle coordinates wherever the coefficient
trivializations are valid (`TauCeti.inCoordinates_pairedWedge`).
-/

public section

open Bundle

namespace TauCeti

variable {FW F₁ F₂ F₃ M : Type*} [TopologicalSpace M] [NormedAddCommGroup FW] [NormedSpace ℝ FW]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃] {W V₁ V₂ V₃ : M → Type*}
  [∀ x, AddCommGroup (W x)] [∀ x, Module ℝ (W x)] [∀ x, TopologicalSpace (W x)]
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module ℝ (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module ℝ (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module ℝ (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace FW W)] [FiberBundle FW W] [VectorBundle ℝ FW W]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle ℝ F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle ℝ F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle ℝ F₃ V₃]
  [∀ x, IsTopologicalAddGroup (V₃ x)] [∀ x, ContinuousSMul ℝ (V₃ x)]

/-- Coordinate expression of a fibrewise paired wedge in valid coefficient trivializations. -/
theorem inCoordinates_pairedWedge {k l : ℕ} {x₀ y : M}
    (μ : V₁ y →L[ℝ] V₂ y →L[ℝ] V₃ y) (hμ : Continuous (Function.uncurry fun a b ↦ μ a b))
    (φ : W y [⋀^Fin k]→L[ℝ] V₁ y) (ψ : W y [⋀^Fin l]→L[ℝ] V₂ y)
    (h₁ : y ∈ (trivializationAt F₁ V₁ x₀).baseSet) (h₂ : y ∈ (trivializationAt F₂ V₂ x₀).baseSet)
    (h₃ : y ∈ (trivializationAt F₃ V₃ x₀).baseSet) :
    ContinuousAlternatingMap.inCoordinates FW F₃ x₀ y x₀ y
        (ContinuousAlternatingMap.pairedWedge μ hμ φ ψ) =
      ContinuousAlternatingMap.pairedWedgeCLM
        (ContinuousLinearMap.inCoordinates F₁ V₁ (F₂ →L[ℝ] F₃)
          (fun z ↦ V₂ z →L[ℝ] V₃ z) x₀ y x₀ y μ)
        (ContinuousAlternatingMap.inCoordinates FW F₁ x₀ y x₀ y φ)
        (ContinuousAlternatingMap.inCoordinates FW F₂ x₀ y x₀ y ψ) := by
  ext v; simp only [ContinuousAlternatingMap.pairedWedgeCLM_apply,
    ContinuousAlternatingMap.inCoordinates, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    ContinuousAlternatingMap.pairedWedge_apply, map_smul, map_sum]
  congr 2; funext σ; rw [ContinuousLinearMap.map_smul_of_tower, inCoordinates_apply_eq₂ h₁ h₂ h₃]
  simp only [Trivialization.continuousLinearMapAt_apply, Trivialization.symm_linearMapAt _ h₁,
    Trivialization.symm_linearMapAt _ h₂, Function.comp_def]

end TauCeti
