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
The corresponding range-transport theorem identifies the subspaces in different
charts, as required for quotient-bundle coordinate changes.

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

/-- Changing tangent or bundle coordinates transports an operator range by the target
coordinate change. The source coordinate change is surjective and leaves the range unchanged. -/
theorem map_range_inCoordinates_coordChangeL [RingHomSurjective σ] {x₀ x₁ x : B} {y₀ y₁ y : B'}
    (ϕ : V x →SL[σ] W y)
    (hx₀ : x ∈ (trivializationAt F V x₀).baseSet)
    (hx₁ : x ∈ (trivializationAt F V x₁).baseSet)
    (hy₀ : y ∈ (trivializationAt F' W y₀).baseSet)
    (hy₁ : y ∈ (trivializationAt F' W y₁).baseSet) :
    (inCoordinates F V F' W x₀ x y₀ y ϕ).range.map
      ((trivializationAt F' W y₀).coordChangeL 𝕜'
        (trivializationAt F' W y₁) y).toLinearMap =
      (inCoordinates F V F' W x₁ x y₁ y ϕ).range := by
  rw [inCoordinates_eq_coordChangeL_comp ϕ hx₁ hx₀ hy₁ hy₀,
    ContinuousLinearMap.toLinearMap_comp, LinearMap.range_comp,
    ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp]
  have hS : ((trivializationAt F V x₁).coordChangeL 𝕜
      (trivializationAt F V x₀) x).toLinearMap.range = ⊤ :=
    LinearMap.range_eq_top.mpr ((trivializationAt F V x₁).coordChangeL 𝕜
      (trivializationAt F V x₀) x).surjective
  -- The coordinate equivalence is coerced through a continuous linear map in the range.
  erw [hS]
  rw [Submodule.map_top]
  rfl

end ContinuousLinearMap
