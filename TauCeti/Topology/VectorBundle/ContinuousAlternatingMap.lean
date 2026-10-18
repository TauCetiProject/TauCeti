/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.ContinuousAlternatingMap
public import Mathlib.Topology.VectorBundle.Hom

/-!
# Composition in alternating-bundle coordinates

Precomposing a fibrewise alternating map with a fibrewise linear map commutes with passing
into bundle coordinates wherever the intermediate trivialization is valid. This identity
allows regularity of pullbacks to be checked on fixed model fibres, without choosing norms
on the original fibres.

The coordinate maps are Mathlib's `ContinuousAlternatingMap.inCoordinates` and
`ContinuousLinearMap.inCoordinates`.
-/

public section

open Bundle

namespace ContinuousAlternatingMap

variable {𝕜 ι B₁ B₂ B₃ F₁ F₂ F₃ : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B₁] [TopologicalSpace B₂] [TopologicalSpace B₃]
  [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
  {V₁ : B₁ → Type*} {V₂ : B₂ → Type*} {V₃ : B₃ → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, AddCommGroup (V₃ x)] [∀ x, Module 𝕜 (V₃ x)] [∀ x, TopologicalSpace (V₃ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  [TopologicalSpace (TotalSpace F₂ V₂)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [TopologicalSpace (TotalSpace F₃ V₃)] [FiberBundle F₃ V₃] [VectorBundle 𝕜 F₃ V₃]

/-- Coordinates of precomposition are precomposition of coordinates. Only the intermediate
fibre must belong to its chosen trivialization's base set. -/
theorem inCoordinates_compContinuousLinearMap {x₀ x : B₁} {y₀ y : B₂} {z₀ z : B₃}
    (φ : V₂ y [⋀^ι]→L[𝕜] V₃ z) (A : V₁ x →L[𝕜] V₂ y)
    (hy : y ∈ (trivializationAt F₂ V₂ y₀).baseSet) :
    inCoordinates F₁ F₃ x₀ x z₀ z (φ.compContinuousLinearMap A) =
      (inCoordinates F₂ F₃ y₀ y z₀ z φ).compContinuousLinearMap
        (ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ x₀ x y₀ y A) := by
  ext v
  simp only [inCoordinates, ContinuousLinearMap.inCoordinates,
    compContinuousLinearMap_apply, ContinuousLinearMap.compContinuousAlternatingMap_coe,
    Function.comp_def, ContinuousLinearMap.coe_comp]
  simp only [Trivialization.symmL_continuousLinearMapAt _ hy]

end ContinuousAlternatingMap
