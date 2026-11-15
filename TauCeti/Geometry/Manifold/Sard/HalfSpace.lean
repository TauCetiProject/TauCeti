/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Sard.Basic

import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Topology.Compactness.Lindelof
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Sard's theorem for manifolds with boundary

Let `f : M → N` be a `C^k` map from a Lindelöf manifold `M` with boundary, modelled on the
`d`-dimensional Euclidean half-space `𝓡∂ d` (`d ≥ 1`), to a manifold `N` (possibly with boundary or
corners) modelled on a finite-dimensional real normed space `E'` of dimension `d'`. When
`k > d - d'` and `k ≥ 1`, the image of the non-regular points of `f` — boundary points included —
is null in `N` (`TauCeti.IsNullSet`), so the regular values of `f` are dense.

In coordinates, the flat Morse–Sard theorem requires openness of the domain (or `ContDiffAt` at each
point), which holds automatically at interior points of `M`
(`TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_isInteriorPoint`) but not at
boundary points, where the extended chart target is only a half-space. Instead, the boundary
`(𝓡∂ (m + 1)).boundary M` carries a canonical `C^k` boundaryless manifold structure of dimension
`m` whose inclusion `ι : ∂M → M` is a `C^k` closed embedding
(`TauCeti.isSmoothEmbedding_subtypeVal_boundary`). By the chain rule
(`TauCeti.IsRegularPoint.of_comp`), every boundary point `p ∈ ∂M` that is non-regular for `f` on `M`
is also non-regular for the restriction `f ∘ ι : ∂M → N`, where the boundaryless Sard theorem
applies at regularity `k > m - d'`, hence a fortiori at `k > (m + 1) - d'`.

The same boundary decomposition extends to products of half-space manifolds with boundaryless
manifolds (`(𝓡∂ d).prod I₂` and `I₁.prod (𝓡∂ d)`, such as parameter spaces `M × S` in parametric
transversality) and to products of two half-space manifolds (`(𝓡∂ d₁).prod (𝓡∂ d₂)`, such as
bordism cylinders `M × [0, 1]`, whose corners of depth two are covered by `(univ ×ˢ ∂M₂)` and
`(∂M₁ ×ˢ univ)`).

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_halfSpace`, and
  `ContMDiff.dense_isRegularValue_halfSpace`: Sard's theorem at the sharp regularity `k > d - d'`,
  `k ≥ 1`, for manifolds modelled on `EuclideanHalfSpace d`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace_prod`,
  `ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod`, and
  `ContMDiff.dense_isRegularValue_halfSpace_prod`: Sard's theorem for products `M₁ × M₂` modelled on
  `(𝓡∂ d).prod I₂` with `M₂` boundaryless.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_prod_halfSpace`, and
  `ContMDiff.dense_isRegularValue_prod_halfSpace`: Sard's theorem for products `M₁ × M₂` modelled on
  `I₁.prod (𝓡∂ d)` with `M₁` boundaryless.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace_prod_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod_halfSpace`, and
  `ContMDiff.dense_isRegularValue_halfSpace_prod_halfSpace`: Sard's theorem for products `M₁ × M₂`
  modelled on `(𝓡∂ d₁).prod (𝓡∂ d₂)`.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* M. W. Hirsch, *Differential Topology*, Graduate Texts in Mathematics 33, Springer, 1976,
  Chapter 3, §1 (Sard's theorem on manifolds with boundary).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10.
-/

public section

open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω} [IsManifold J n N]

section HalfSpace

variable {d : ℕ} [NeZero d]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M] [LindelofSpace M]
  [IsManifold (𝓡∂ d) n M] {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with boundary.** Let `M` be a Lindelöf manifold modelled on the
`d`-dimensional Euclidean half-space `𝓡∂ d` and `N` a manifold modelled on a space of dimension
`d'`. If `f` is `C^k` at every point of `s` with `k > d - d'` and `k ≥ 1`, and no point of `s` is
regular, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace
    (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡∂ d) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡∂ d) J f x) :
    IsNullSet J (f '' s) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : IsManifold (𝓡∂ (m + 1)) 1 M := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) n ↥((𝓡∂ (m + 1)).boundary M) :=
    isManifold_boundary M hn
  have : LindelofSpace ↥((𝓡∂ (m + 1)).boundary M) :=
    ((𝓡∂ (m + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
  have hk₀ : ((finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
    simpa [finrank_euclideanSpace_fin] using hk
  have hk' : ((finrank ℝ (EuclideanSpace ℝ (Fin m)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
    (Nat.cast_le.2 (by rw [finrank_euclideanSpace_fin]; omega)).trans hk
  exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_range
    (K := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (g := (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M) → M)) hk₀ hf hs
    (inter_subset_right.trans (by simp))
    (fun b _ ↦ (isSmoothEmbedding_subtypeVal_boundary M hn).contMDiff b)
    fun _ hft hst ↦ isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk' hft hst

/-- **Sard's theorem for manifolds with boundary.** The critical values of a `C^k` map from a
Lindelöf manifold modelled on `EuclideanHalfSpace d` to a manifold of dimension `d'` form a null set
when `k > d - d'` and `k ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace
    (hf : ContMDiff (𝓡∂ d) J n f) (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡∂ d) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map from a Lindelöf manifold modelled on `EuclideanHalfSpace d`
to a manifold of dimension `d'` are dense when `k > d - d'` and `k ≥ 1`, in particular when the map
is smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace
    (hf : ContMDiff (𝓡∂ d) J n f) (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (𝓡∂ d) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace hk).dense_compl

end HalfSpace

section ProdBoundarylessRight

variable {d : ℕ} [NeZero d]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace d) M₁] [LindelofSpace M₁]
  [IsManifold (𝓡∂ d) n M₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [LindelofSpace M₂]
  [BoundarylessManifold I₂ M₂] [IsManifold I₂ n M₂]
  {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}

/-- **Sard's theorem for a product of a manifold with boundary and a boundaryless manifold.** -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace_prod
    (hk : ((d + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡∂ d).prod I₂) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡∂ d).prod I₂) J f x) :
    IsNullSet J (f '' s) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : SecondCountableTopology (EuclideanHalfSpace (m + 1)) :=
    (𝓡∂ (m + 1)).secondCountableTopology
  have : SecondCountableTopology M₁ :=
    ChartedSpace.secondCountable_of_lindelof (EuclideanHalfSpace (m + 1)) M₁
  have : SecondCountableTopology H₂ := I₂.secondCountableTopology
  have : SecondCountableTopology M₂ := ChartedSpace.secondCountable_of_lindelof H₂ M₂
  have : IsManifold (𝓡∂ (m + 1)) 1 M₁ := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) n ↥((𝓡∂ (m + 1)).boundary M₁) :=
    isManifold_boundary M₁ hn
  have hk₀ :
      ((finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)) × E₂) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
    simpa [finrank_euclideanSpace_fin] using hk
  have hk' :
      ((finrank ℝ (EuclideanSpace ℝ (Fin m) × E₂) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
    (Nat.cast_le.2 (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin]; omega)).trans hk
  refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_range
    (K := 𝓘(ℝ, EuclideanSpace ℝ (Fin m)).prod I₂)
    (g := Prod.map (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M₁) → M₁) (id : M₂ → M₂)) hk₀ hf hs ?_
    (fun b _ ↦ ((isSmoothEmbedding_subtypeVal_boundary M₁ hn).contMDiff.prodMap contMDiff_id) b)
    fun _ hft hst ↦ isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk' hft hst
  rw [ModelWithCorners.boundary_of_boundaryless_right, range_prodMap, Subtype.range_coe, range_id]
  exact inter_subset_right

/-- **Sard's theorem** for a `C^k` map on `M₁ × M₂`, with `M₁` modelled on `EuclideanHalfSpace d`
and `M₂` boundaryless. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod
    (hf : ContMDiff ((𝓡∂ d).prod I₂) J n f)
    (hk : ((d + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡∂ d).prod I₂) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace_prod hk (fun x _ ↦ hf x)
    fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on `M₁ × M₂`, with `M₁` modelled on `EuclideanHalfSpace d`
and `M₂` boundaryless, are dense when `k > d + dim M₂ - d'` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace_prod
    (hf : ContMDiff ((𝓡∂ d).prod I₂) J n f)
    (hk : ((d + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡∂ d).prod I₂) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace_prod hk).dense_compl

end ProdBoundarylessRight

section ProdBoundarylessLeft

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [LindelofSpace M₁]
  [BoundarylessManifold I₁ M₁] [IsManifold I₁ n M₁]
  {d : ℕ} [NeZero d]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace d) M₂] [LindelofSpace M₂]
  [IsManifold (𝓡∂ d) n M₂]
  {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}

/-- **Sard's theorem for a product of a boundaryless manifold and a manifold with boundary.** -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_halfSpace
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod (𝓡∂ d)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod (𝓡∂ d)) J f x) :
    IsNullSet J (f '' s) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : SecondCountableTopology H₁ := I₁.secondCountableTopology
  have : SecondCountableTopology M₁ := ChartedSpace.secondCountable_of_lindelof H₁ M₁
  have : SecondCountableTopology (EuclideanHalfSpace (m + 1)) :=
    (𝓡∂ (m + 1)).secondCountableTopology
  have : SecondCountableTopology M₂ :=
    ChartedSpace.secondCountable_of_lindelof (EuclideanHalfSpace (m + 1)) M₂
  have : IsManifold (𝓡∂ (m + 1)) 1 M₂ := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) n ↥((𝓡∂ (m + 1)).boundary M₂) :=
    isManifold_boundary M₂ hn
  have hk₀ :
      ((finrank ℝ (E₁ × EuclideanSpace ℝ (Fin (m + 1))) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
    simpa [finrank_euclideanSpace_fin] using hk
  have hk' :
      ((finrank ℝ (E₁ × EuclideanSpace ℝ (Fin m)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
    (Nat.cast_le.2 (by simp only [Module.finrank_prod, finrank_euclideanSpace_fin]; omega)).trans hk
  refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_range
    (K := I₁.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin m)))
    (g := Prod.map (id : M₁ → M₁) (Subtype.val : ↥((𝓡∂ (m + 1)).boundary M₂) → M₂)) hk₀ hf hs ?_
    (fun b _ ↦ (contMDiff_id.prodMap (isSmoothEmbedding_subtypeVal_boundary M₂ hn).contMDiff) b)
    fun _ hft hst ↦ isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk' hft hst
  rw [ModelWithCorners.boundary_of_boundaryless_left, range_prodMap, range_id, Subtype.range_coe]
  exact inter_subset_right

/-- **Sard's theorem** for a `C^k` map on `M₁ × M₂`, with `M₁` boundaryless and `M₂` modelled on
`EuclideanHalfSpace d`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_prod_halfSpace
    (hf : ContMDiff (I₁.prod (𝓡∂ d)) J n f)
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (I₁.prod (𝓡∂ d)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_halfSpace hk (fun x _ ↦ hf x)
    fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on `M₁ × M₂`, with `M₁` boundaryless and `M₂` modelled on
`EuclideanHalfSpace d`, are dense when `k > dim M₁ + d - d'` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_prod_halfSpace
    (hf : ContMDiff (I₁.prod (𝓡∂ d)) J n f)
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (I₁.prod (𝓡∂ d)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_prod_halfSpace hk).dense_compl

end ProdBoundarylessLeft

section ProdHalfSpace

variable {d₁ : ℕ} [NeZero d₁]
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace d₁) M₁] [LindelofSpace M₁]
  [IsManifold (𝓡∂ d₁) n M₁]
  {d₂ : ℕ} [NeZero d₂]
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace d₂) M₂] [LindelofSpace M₂]
  [IsManifold (𝓡∂ d₂) n M₂]
  {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}

/-- **Sard's theorem for a product of two manifolds with boundary.** Such a product (for instance a
bordism cylinder `M × [0, 1]`) has corners of depth two along `∂M₁ × ∂M₂`, covered by the two
hypersurface pieces `M₁ × ∂M₂` and `∂M₁ × M₂`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace_prod_halfSpace
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡∂ d₁).prod (𝓡∂ d₂)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡∂ d₁).prod (𝓡∂ d₂)) J f x) :
    IsNullSet J (f '' s) := by
  obtain ⟨m₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d₁)
  obtain ⟨m₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d₂)
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : SecondCountableTopology (EuclideanHalfSpace (m₁ + 1)) :=
    (𝓡∂ (m₁ + 1)).secondCountableTopology
  have : SecondCountableTopology M₁ :=
    ChartedSpace.secondCountable_of_lindelof (EuclideanHalfSpace (m₁ + 1)) M₁
  have : SecondCountableTopology (EuclideanHalfSpace (m₂ + 1)) :=
    (𝓡∂ (m₂ + 1)).secondCountableTopology
  have : SecondCountableTopology M₂ :=
    ChartedSpace.secondCountable_of_lindelof (EuclideanHalfSpace (m₂ + 1)) M₂
  have : IsManifold (𝓡∂ (m₁ + 1)) 1 M₁ := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m₁)) n ↥((𝓡∂ (m₁ + 1)).boundary M₁) :=
    isManifold_boundary M₁ hn
  have : IsManifold (𝓡∂ (m₂ + 1)) 1 M₂ := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m₂)) n ↥((𝓡∂ (m₂ + 1)).boundary M₂) :=
    isManifold_boundary M₂ hn
  have hk₀ : ((finrank ℝ (EuclideanSpace ℝ (Fin (m₁ + 1)) × EuclideanSpace ℝ (Fin (m₂ + 1))) -
      finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
    simpa [finrank_euclideanSpace_fin] using hk
  have hk₁ :
      ((m₁ + 1 + finrank ℝ (EuclideanSpace ℝ (Fin m₂)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
    (Nat.cast_le.2 (by rw [finrank_euclideanSpace_fin]; omega)).trans hk
  have hk₂ :
      ((finrank ℝ (EuclideanSpace ℝ (Fin m₁)) + (m₂ + 1) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
    (Nat.cast_le.2 (by rw [finrank_euclideanSpace_fin]; omega)).trans hk
  refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_union_range
    (K₁ := (𝓡∂ (m₁ + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin m₂)))
    (g₁ := Prod.map (id : M₁ → M₁) (Subtype.val : ↥((𝓡∂ (m₂ + 1)).boundary M₂) → M₂))
    (K₂ := 𝓘(ℝ, EuclideanSpace ℝ (Fin m₁)).prod (𝓡∂ (m₂ + 1)))
    (g₂ := Prod.map (Subtype.val : ↥((𝓡∂ (m₁ + 1)).boundary M₁) → M₁) (id : M₂ → M₂))
    hk₀ hf hs ?_
    (fun b _ ↦ (contMDiff_id.prodMap (isSmoothEmbedding_subtypeVal_boundary M₂ hn).contMDiff) b)
    (fun b _ ↦ ((isSmoothEmbedding_subtypeVal_boundary M₁ hn).contMDiff.prodMap contMDiff_id) b)
    (fun _ hft hst ↦
      isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace_prod hk₁ hft hst)
    (fun _ hft hst ↦
      isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_halfSpace hk₂ hft hst)
  rw [ModelWithCorners.boundary_prod, range_prodMap, range_prodMap, range_id, range_id,
    Subtype.range_coe, Subtype.range_coe]
  exact inter_subset_right

/-- **Sard's theorem** for a `C^k` map on a product `M₁ × M₂` of two Lindelöf manifolds with
boundary. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod_halfSpace
    (hf : ContMDiff ((𝓡∂ d₁).prod (𝓡∂ d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡∂ d₁).prod (𝓡∂ d₂)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_halfSpace_prod_halfSpace hk
    (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on a product `M₁ × M₂` of two Lindelöf manifolds with
boundary are dense when `k > d₁ + d₂ - d'` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace_prod_halfSpace
    (hf : ContMDiff ((𝓡∂ d₁).prod (𝓡∂ d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡∂ d₁).prod (𝓡∂ d₂)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace_prod_halfSpace hk).dense_compl

end ProdHalfSpace

end TauCeti
