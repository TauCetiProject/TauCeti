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
`ContinuousLinearMap.isInvertible_inCoordinates_iff` reads invertibility of a fibre map
off its coordinate expression, and `ContinuousLinearMap.inCoordinates_comp` reads a composite
of fibre maps as the composite of their coordinate expressions.

`VectorBundleCore.localTriv_coordChangeL` and
`VectorBundleCore.trivializationAt_coordChangeL` identify transitions between actual
trivializations with their core coordinate-change maps.
The fibre instances `VectorBundleCore.isTopologicalAddGroupFiber` and
`VectorBundleCore.continuousSMulFiber` make Mathlib's Hom bundle between two cores available.
`VectorBundleCore.inChartCoordinates` expresses a fibre map between two cores in an arbitrary
pair of source and target charts, not only the preferred charts of base points, and
`VectorBundleCore.inChartCoordinates_comp` composes these expressions through any intermediate
chart containing the base point.

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

/-- The fibres of a vector bundle core are topological additive groups, as is the model fibre.
This makes the Hom bundle between two cores available. -/
instance isTopologicalAddGroupFiber (Z : VectorBundleCore 𝕜 B F κ) (x : B) :
    IsTopologicalAddGroup (Z.Fiber x) :=
  inferInstanceAs (IsTopologicalAddGroup F)

/-- Scalar multiplication on the fibres of a vector bundle core is continuous. -/
instance continuousSMulFiber (Z : VectorBundleCore 𝕜 B F κ) (x : B) :
    ContinuousSMul 𝕜 (Z.Fiber x) :=
  inferInstanceAs (ContinuousSMul 𝕜 F)

section inChartCoordinates

variable {G H ι ν : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The expression of a fibre map `ϕ` over `x` in the source chart `i` and the target chart
`j`. Unlike `ContinuousLinearMap.inCoordinates`, the charts need not be preferred charts of
base points. -/
def inChartCoordinates (Z : VectorBundleCore 𝕜 B F ι) (W : VectorBundleCore 𝕜 B G κ)
    (i : ι) (j : κ) (x : B) (ϕ : F →L[𝕜] G) : F →L[𝕜] G :=
  (W.coordChange (W.indexAt x) j x).comp (ϕ.comp (Z.coordChange i (Z.indexAt x) x))

variable (Z : VectorBundleCore 𝕜 B F ι) (W : VectorBundleCore 𝕜 B G κ)
  (V : VectorBundleCore 𝕜 B H ν)

@[simp] theorem inChartCoordinates_apply (i : ι) (j : κ) (x : B) (ϕ : F →L[𝕜] G) (v : F) :
    Z.inChartCoordinates W i j x ϕ v =
      W.coordChange (W.indexAt x) j x (ϕ (Z.coordChange i (Z.indexAt x) x v)) := (rfl)

/-- In the preferred charts the coordinate expression of a fibre map is the map itself. -/
@[simp] theorem inChartCoordinates_indexAt (x : B) (ϕ : F →L[𝕜] G) :
    Z.inChartCoordinates W (Z.indexAt x) (W.indexAt x) x ϕ = ϕ := by
  ext v
  simp [Z.coordChange_self _ x (Z.mem_baseSet_at x),
    W.coordChange_self _ x (W.mem_baseSet_at x)]

/-- Coordinate expressions of a composite compose through any intermediate chart containing
the base point. -/
theorem inChartCoordinates_comp (i : ι) {j : κ} (k : ν) {x : B} (hj : x ∈ W.baseSet j)
    (ψ : G →L[𝕜] H) (ϕ : F →L[𝕜] G) :
    Z.inChartCoordinates V i k x (ψ.comp ϕ) =
      (W.inChartCoordinates V j k x ψ).comp (Z.inChartCoordinates W i j x ϕ) := by
  ext v
  simp only [inChartCoordinates_apply, ContinuousLinearMap.comp_apply,
    W.coordChange_comp _ j _ x ⟨⟨W.mem_baseSet_at x, hj⟩, W.mem_baseSet_at x⟩,
    W.coordChange_self _ x (W.mem_baseSet_at x)]

end inChartCoordinates

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

/-- In trivializations whose base sets contain the two fibre base points, a continuous linear
map between fibres is invertible exactly when its coordinate expression is. -/
theorem isInvertible_inCoordinates_iff {x₀ x : B} {y₀ y : B'} {ϕ : V x →L[𝕜] W y}
    (hx : x ∈ (trivializationAt F V x₀).baseSet)
    (hy : y ∈ (trivializationAt F' W y₀).baseSet) :
    (inCoordinates F V F' W x₀ x y₀ y ϕ).IsInvertible ↔ ϕ.IsInvertible := by
  rw [inCoordinates_eq hx hy, isInvertible_equiv_comp, isInvertible_comp_equiv]

end Inverse

section Comp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {B : Type*} [TopologicalSpace B] {B' : Type*} [TopologicalSpace B']
  {B'' : Type*} [TopologicalSpace B'']
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {F'' : Type*} [NormedAddCommGroup F''] [NormedSpace 𝕜 F'']
  {V : B → Type*} [∀ x, AddCommMonoid (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {W : B' → Type*} [∀ x, AddCommMonoid (W x)] [∀ x, Module 𝕜 (W x)]
  [∀ x, TopologicalSpace (W x)] [TopologicalSpace (TotalSpace F' W)]
  [FiberBundle F' W] [VectorBundle 𝕜 F' W]
  {U : B'' → Type*} [∀ x, AddCommMonoid (U x)] [∀ x, Module 𝕜 (U x)]
  [∀ x, TopologicalSpace (U x)] [TopologicalSpace (TotalSpace F'' U)]
  [FiberBundle F'' U] [VectorBundle 𝕜 F'' U]

/-- The coordinate expression of a composite is the composite of the coordinate expressions,
provided the trivialization of the middle bundle contains the middle fibre base point. -/
theorem inCoordinates_comp {x₀ x : B} {y₀ y : B'} {z₀ z : B''}
    (ψ : W y →L[𝕜] U z) (ϕ : V x →L[𝕜] W y) (hy : y ∈ (trivializationAt F' W y₀).baseSet) :
    inCoordinates F V F'' U x₀ x z₀ z (ψ.comp ϕ) =
      (inCoordinates F' W F'' U y₀ y z₀ z ψ).comp (inCoordinates F V F' W x₀ x y₀ y ϕ) := by
  ext v
  simp only [inCoordinates, comp_apply, Trivialization.symmL_continuousLinearMapAt _ hy]

end Comp

end ContinuousLinearMap
