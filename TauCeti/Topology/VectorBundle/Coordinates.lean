/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic

/-!
# Changing the coordinates of a bundle homomorphism

`ContinuousLinearMap.inCoordinates_eq_coordChangeL_comp` changes both preferred
trivializations used to read a continuous semilinear map between vector-bundle fibres.
The source and target bundles may have different bases. This formula permits regularity
proved in coordinates centred at a point to be transported to fixed trivializations.

The construction follows Mathlib's `ContinuousLinearMap.inCoordinates` and
`Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change`.
-/

public section

open Bundle

namespace ContinuousLinearMap

variable {𝕜 𝕜' : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜']
  {σ : 𝕜 →+* 𝕜'}
  {B : Type*} [TopologicalSpace B] {B' : Type*} [TopologicalSpace B']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜' F']
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {W : B' → Type*} [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜' (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace F' W)]
  [FiberBundle F' W] [VectorBundle 𝕜' F' W]

/-- Changing the source and target trivializations pre- and post-composes the coordinate
operator with the corresponding bundle transitions. All four trivializations must contain their
respective fibre base points. -/
theorem inCoordinates_eq_coordChangeL_comp {x₀ x₁ x : B} {y₀ y₁ y : B'}
    (ϕ : V x →SL[σ] W y)
    (hx₀ : x ∈ (trivializationAt F V x₀).baseSet)
    (hx₁ : x ∈ (trivializationAt F V x₁).baseSet)
    (hy₀ : y ∈ (trivializationAt F' W y₀).baseSet)
    (hy₁ : y ∈ (trivializationAt F' W y₁).baseSet) :
    inCoordinates F V F' W x₀ x y₀ y ϕ =
      ((trivializationAt F' W y₁).coordChangeL 𝕜'
        (trivializationAt F' W y₀) y : F' →L[𝕜'] F').comp
        ((inCoordinates F V F' W x₁ x y₁ y ϕ).comp
          ((trivializationAt F V x₀).coordChangeL 𝕜
            (trivializationAt F V x₁) x : F →L[𝕜] F)) := by
  rw [inCoordinates_eq hx₀ hy₀, inCoordinates_eq hx₁ hy₁,
    ← Trivialization.comp_continuousLinearEquivAt_eq_coord_change _ _ ⟨hy₁, hy₀⟩,
    ← Trivialization.comp_continuousLinearEquivAt_eq_coord_change _ _ ⟨hx₀, hx₁⟩]
  ext v
  simp only [comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.trans_apply, ContinuousLinearEquiv.symm_apply_apply]

end ContinuousLinearMap
