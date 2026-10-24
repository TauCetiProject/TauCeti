/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.VectorBundle.Basic

/-!
# Changing the coordinates of a bundle homomorphism

`ContinuousLinearMap.inCoordinates_eq_coordChangeL_comp` changes both preferred
trivializations used to read a continuous semilinear map between vector-bundle fibres.
The source and target bundles may have different bases. This formula permits regularity
proved in coordinates centred at a point to be transported to fixed trivializations.
The corresponding range-transport theorem identifies the subspaces in different
charts, as required for quotient-bundle coordinate changes.
`ContinuousLinearMap.inCoordinates_inverse` reads the inverse of a fibre map in coordinates
as the inverse of its coordinate expression, which reduces smoothness of fibrewise inverses
to smoothness of inversion of continuous linear maps.

`VectorBundleCore.localTriv_coordChangeL` and
`VectorBundleCore.trivializationAt_coordChangeL` identify transitions between actual
trivializations with their core coordinate-change maps.

The construction follows Mathlib's `ContinuousLinearMap.inCoordinates` and
`Bundle.Trivialization.comp_continuousLinearEquivAt_eq_coord_change`.
-/

public section

open Bundle

namespace VectorBundleCore

variable {𝕜 B F κ : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A transition between core trivializations is the core coordinate-change map. -/
@[simp] theorem localTriv_coordChangeL (Z : VectorBundleCore 𝕜 B F κ) {i j : κ} {x : B}
    (hx : x ∈ (Z.localTriv i).baseSet ∩ (Z.localTriv j).baseSet) :
    ((Z.localTriv i).coordChangeL 𝕜 (Z.localTriv j) x : F →L[𝕜] F) = Z.coordChange i j x := by
  ext v
  exact Z.localTriv_coordChange_eq i j hx v

/-- Preferred core trivializations use their selected core coordinate-change maps. -/
@[simp] theorem trivializationAt_coordChangeL (Z : VectorBundleCore 𝕜 B F κ)
    {α β x : B} (hx : x ∈ (trivializationAt F Z.Fiber α).baseSet ∩
      (trivializationAt F Z.Fiber β).baseSet) :
    ((trivializationAt F Z.Fiber α).coordChangeL 𝕜
      (trivializationAt F Z.Fiber β) x : F →L[𝕜] F) =
        Z.coordChange (Z.indexAt α) (Z.indexAt β) x := by
  ext v
  exact Z.trivializationAt_coordChange_eq hx v

end VectorBundleCore

namespace ContinuousLinearMap

section CoordChange

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

end CoordChange

section Inverse

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B] {B' : Type*} [TopologicalSpace B']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {W : B' → Type*} [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace F' W)]
  [FiberBundle F' W] [VectorBundle 𝕜 F' W]

/-- In trivializations whose base sets contain the two fibre base points, the inverse of a
continuous linear map between fibres reads as the inverse of its coordinate expression. No
invertibility is assumed: both sides vanish when the map is not invertible. -/
theorem inCoordinates_inverse {x₀ x : B} {y₀ y : B'} (ϕ : V x →L[𝕜] W y)
    (hx : x ∈ (trivializationAt F V x₀).baseSet)
    (hy : y ∈ (trivializationAt F' W y₀).baseSet) :
    inCoordinates F' W F V y₀ y x₀ x ϕ.inverse =
      (inCoordinates F V F' W x₀ x y₀ y ϕ).inverse := by
  rw [inCoordinates_eq hy hx, inCoordinates_eq hx hy, inverse_equiv_comp, inverse_comp_equiv,
    ContinuousLinearEquiv.symm_symm, comp_assoc]

end Inverse

end ContinuousLinearMap
