/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Corners.AbstractBoundary.Manifold
public import TauCeti.Geometry.Manifold.Sard.Basic

import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Topology.Compactness.Lindelof
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Sard's theorem for manifolds with corners

Let `f : M → N` be a `C^k` map from a Lindelöf manifold with corners `M`, modelled on the
`d`-dimensional Euclidean quadrant `𝓡c d`, to a manifold `N` (possibly with boundary or corners)
modelled on a finite-dimensional real normed space `E'` of dimension `d'`. When `k > d - d'` and
`k ≥ 1`, the image of the non-regular points of `f` across the interior and all boundary faces and
corner strata of `M` is null in `N` (`TauCeti.IsNullSet`), so the regular values of `f` are dense.

Unlike the boundary of a manifold modelled on the half-space, the topological boundary
`(𝓡c (m + 1)).boundary M` is not a manifold at corners of depth at least two. Instead, the
induction on the dimension `d` passes through Joyce's abstract boundary
`(𝓡c (m + 1)).AbstractBoundary M` (`TauCeti.Geometry.Manifold.Corners.AbstractBoundary.Manifold`),
which is a `C^k` Lindelöf manifold with corners modelled on `𝓡c m` one dimension down
(`ModelWithCorners.AbstractBoundary.isManifold`,
`ModelWithCorners.AbstractBoundary.lindelofSpace`), equipped with a `C^k` projection
`ModelWithCorners.AbstractBoundary.point` onto `(𝓡c (m + 1)).boundary M`
(`ModelWithCorners.AbstractBoundary.contMDiff_point`,
`ModelWithCorners.AbstractBoundary.range_point`). At the base `d = 0`, the model `𝓡c 0` is
boundaryless (`TauCeti.modelWithCornersEuclideanQuadrant_zero_boundaryless`), so the boundaryless
Sard theorem applies. At the induction step `d = m + 1`, interior critical points are handled in
coordinates (`TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_isInteriorPoint`),
while boundary critical points lift to non-regular points of `f ∘ point` on the abstract boundary
by `TauCeti.IsRegularPoint.of_comp` and are handled by the induction hypothesis at `k > m - d'`.

The same induction applies to products `(𝓡c d).prod I₂`, `I₁.prod (𝓡c d)` with a boundaryless
factor, and `(𝓡c d₁).prod (𝓡c d₂)` of two manifolds with corners.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_quadrant`, and
  `ContMDiff.dense_isRegularValue_quadrant`: Sard's theorem at the sharp regularity `k > d - d'`,
  `k ≥ 1`, for manifolds with corners modelled on `EuclideanQuadrant d`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant_prod`,
  `ContMDiff.isNullSet_image_criticalPoints_quadrant_prod`, and
  `ContMDiff.dense_isRegularValue_quadrant_prod`: Sard's theorem for products `M₁ × M₂` modelled on
  `(𝓡c d).prod I₂` with `M₂` boundaryless.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_prod_quadrant`, and
  `ContMDiff.dense_isRegularValue_prod_quadrant`: Sard's theorem for products `M₁ × M₂` modelled on
  `I₁.prod (𝓡c d)` with `M₁` boundaryless.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant_prod_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_quadrant_prod_quadrant`, and
  `ContMDiff.dense_isRegularValue_quadrant_prod_quadrant`: Sard's theorem for products `M₁ × M₂`
  modelled on `(𝓡c d₁).prod (𝓡c d₂)`.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press, 2012, 225–258, Section 2 (abstract boundary `∂X`).
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 and Chapter 16 (*Manifolds with Corners*).
-/

public section

open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {n : ℕ∞ω} [IsManifold J n N]

section Quadrant

/-- **Sard's theorem for manifolds with corners.** Let `M` be a Lindelöf manifold with corners
modelled on the `d`-dimensional Euclidean quadrant `𝓡c d` and `N` a manifold modelled on a space of
dimension `d'`. If `f` is `C^k` at every point of `s` with `k > d - d'` and `k ≥ 1`, and no point of
`s` is regular, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant {d : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M] [LindelofSpace M]
    [IsManifold (𝓡c d) n M] {f : M → N} {s : Set M}
    (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡c d) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡c d) J f x) :
    IsNullSet J (f '' s) := by
  induction d generalizing M with
  | zero =>
    have hk₀ : ((finrank ℝ (EuclideanSpace ℝ (Fin 0)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa [finrank_euclideanSpace_fin] using hk
    exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk₀ hf hs
  | succ m ih =>
    have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
    have : LindelofSpace ((𝓡c (m + 1)).AbstractBoundary M) :=
      ModelWithCorners.AbstractBoundary.lindelofSpace
        (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn
    have hk₀ :
        ((finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa [finrank_euclideanSpace_fin] using hk
    have hk' : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
      (Nat.cast_le.2 (by omega)).trans hk
    refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_range
      (K := 𝓡c m) (g := (ModelWithCorners.AbstractBoundary.point :
        (𝓡c (m + 1)).AbstractBoundary M → M)) hk₀ hf hs ?_
      (fun b _ ↦ ModelWithCorners.AbstractBoundary.contMDiff_point b)
      fun _ hft hst ↦ ih hk' hft hst
    rw [ModelWithCorners.AbstractBoundary.range_point
      (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn]
    exact inter_subset_right

/-- **Sard's theorem for manifolds with corners.** The critical values of a `C^k` map from a
Lindelöf manifold with corners modelled on `EuclideanQuadrant d` to a manifold of dimension `d'`
form a null set when `k > d - d'` and `k ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant {d : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M] [LindelofSpace M]
    [IsManifold (𝓡c d) n M] {f : M → N}
    (hf : ContMDiff (𝓡c d) J n f) (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡c d) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map from a Lindelöf manifold with corners modelled on
`EuclideanQuadrant d` to a manifold of dimension `d'` are dense when `k > d - d'` and `k ≥ 1`, in
particular when the map is smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant {d : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M] [LindelofSpace M]
    [IsManifold (𝓡c d) n M] {f : M → N}
    (hf : ContMDiff (𝓡c d) J n f) (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (𝓡c d) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant hk).dense_compl

end Quadrant

section ProdBoundarylessRight

variable {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂] [LindelofSpace M₂]
  [BoundarylessManifold I₂ M₂] [IsManifold I₂ n M₂]

/-- **Sard's theorem for a product of a manifold with corners and a boundaryless manifold.** -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant_prod {d : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d) M₁] [LindelofSpace M₁]
    [IsManifold (𝓡c d) n M₁] {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hk : ((d + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡c d).prod I₂) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡c d).prod I₂) J f x) :
    IsNullSet J (f '' s) := by
  have : SecondCountableTopology H₂ := I₂.secondCountableTopology
  have : SecondCountableTopology M₂ := ChartedSpace.secondCountable_of_lindelof H₂ M₂
  induction d generalizing M₁ with
  | zero =>
    have : SecondCountableTopology (EuclideanQuadrant 0) := (𝓡c 0).secondCountableTopology
    have : SecondCountableTopology M₁ :=
      ChartedSpace.secondCountable_of_lindelof (EuclideanQuadrant 0) M₁
    have hk₀ :
        ((finrank ℝ (EuclideanSpace ℝ (Fin 0) × E₂) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa [finrank_euclideanSpace_fin] using hk
    exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk₀ hf hs
  | succ m ih =>
    have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
    have : SecondCountableTopology (EuclideanQuadrant (m + 1)) :=
      (𝓡c (m + 1)).secondCountableTopology
    have : SecondCountableTopology M₁ :=
      ChartedSpace.secondCountable_of_lindelof (EuclideanQuadrant (m + 1)) M₁
    have : SecondCountableTopology ((𝓡c (m + 1)).AbstractBoundary M₁) :=
      ModelWithCorners.AbstractBoundary.secondCountableTopology
        (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn
    have hk₀ :
        ((finrank ℝ (EuclideanSpace ℝ (Fin (m + 1)) × E₂) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa [finrank_euclideanSpace_fin] using hk
    have hk' : ((m + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
      (Nat.cast_le.2 (by omega)).trans hk
    refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_range
      (K := (𝓡c m).prod I₂)
      (g := Prod.map
        (ModelWithCorners.AbstractBoundary.point : (𝓡c (m + 1)).AbstractBoundary M₁ → M₁)
        (id : M₂ → M₂)) hk₀ hf hs ?_
      (fun b _ ↦ (ModelWithCorners.AbstractBoundary.contMDiff_point.prodMap contMDiff_id) b)
      fun _ hft hst ↦ ih hk' hft hst
    rw [ModelWithCorners.boundary_of_boundaryless_right, range_prodMap,
      ModelWithCorners.AbstractBoundary.range_point
        (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn, range_id]
    exact inter_subset_right

/-- **Sard's theorem** for a `C^k` map on `M₁ × M₂`, with `M₁` modelled on `EuclideanQuadrant d`
and `M₂` boundaryless. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant_prod {d : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d) M₁] [LindelofSpace M₁]
    [IsManifold (𝓡c d) n M₁] {f : M₁ × M₂ → N}
    (hf : ContMDiff ((𝓡c d).prod I₂) J n f)
    (hk : ((d + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡c d).prod I₂) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant_prod hk (fun x _ ↦ hf x)
    fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on `M₁ × M₂`, with `M₁` modelled on `EuclideanQuadrant d`
and `M₂` boundaryless, are dense when `k > d + dim M₂ - d'` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant_prod {d : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d) M₁] [LindelofSpace M₁]
    [IsManifold (𝓡c d) n M₁] {f : M₁ × M₂ → N}
    (hf : ContMDiff ((𝓡c d).prod I₂) J n f)
    (hk : ((d + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡c d).prod I₂) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant_prod hk).dense_compl

end ProdBoundarylessRight

section ProdBoundarylessLeft

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁] [LindelofSpace M₁]
  [BoundarylessManifold I₁ M₁] [IsManifold I₁ n M₁]

/-- **Sard's theorem for a product of a boundaryless manifold and a manifold with corners.** -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_quadrant {d : ℕ}
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d) M₂] [LindelofSpace M₂]
    [IsManifold (𝓡c d) n M₂] {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod (𝓡c d)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod (𝓡c d)) J f x) :
    IsNullSet J (f '' s) := by
  have : SecondCountableTopology H₁ := I₁.secondCountableTopology
  have : SecondCountableTopology M₁ := ChartedSpace.secondCountable_of_lindelof H₁ M₁
  induction d generalizing M₂ with
  | zero =>
    have : SecondCountableTopology (EuclideanQuadrant 0) := (𝓡c 0).secondCountableTopology
    have : SecondCountableTopology M₂ :=
      ChartedSpace.secondCountable_of_lindelof (EuclideanQuadrant 0) M₂
    have hk₀ :
        ((finrank ℝ (E₁ × EuclideanSpace ℝ (Fin 0)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa [finrank_euclideanSpace_fin] using hk
    exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk₀ hf hs
  | succ m ih =>
    have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
    have : SecondCountableTopology (EuclideanQuadrant (m + 1)) :=
      (𝓡c (m + 1)).secondCountableTopology
    have : SecondCountableTopology M₂ :=
      ChartedSpace.secondCountable_of_lindelof (EuclideanQuadrant (m + 1)) M₂
    have : SecondCountableTopology ((𝓡c (m + 1)).AbstractBoundary M₂) :=
      ModelWithCorners.AbstractBoundary.secondCountableTopology
        (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn
    have hk₀ :
        ((finrank ℝ (E₁ × EuclideanSpace ℝ (Fin (m + 1))) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa [finrank_euclideanSpace_fin] using hk
    have hk' : ((finrank ℝ E₁ + m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
      (Nat.cast_le.2 (by omega)).trans hk
    refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_range
      (K := I₁.prod (𝓡c m))
      (g := Prod.map (id : M₁ → M₁)
        (ModelWithCorners.AbstractBoundary.point : (𝓡c (m + 1)).AbstractBoundary M₂ → M₂))
      hk₀ hf hs ?_
      (fun b _ ↦ (contMDiff_id.prodMap ModelWithCorners.AbstractBoundary.contMDiff_point) b)
      fun _ hft hst ↦ ih hk' hft hst
    rw [ModelWithCorners.boundary_of_boundaryless_left, range_prodMap, range_id,
      ModelWithCorners.AbstractBoundary.range_point
        (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn]
    exact inter_subset_right

/-- **Sard's theorem** for a `C^k` map on `M₁ × M₂`, with `M₁` boundaryless and `M₂` modelled on
`EuclideanQuadrant d`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_prod_quadrant {d : ℕ}
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d) M₂] [LindelofSpace M₂]
    [IsManifold (𝓡c d) n M₂] {f : M₁ × M₂ → N}
    (hf : ContMDiff (I₁.prod (𝓡c d)) J n f)
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (I₁.prod (𝓡c d)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_quadrant hk (fun x _ ↦ hf x)
    fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on `M₁ × M₂`, with `M₁` boundaryless and `M₂` modelled on
`EuclideanQuadrant d`, are dense when `k > dim M₁ + d - d'` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_prod_quadrant {d : ℕ}
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d) M₂] [LindelofSpace M₂]
    [IsManifold (𝓡c d) n M₂] {f : M₁ × M₂ → N}
    (hf : ContMDiff (I₁.prod (𝓡c d)) J n f)
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (I₁.prod (𝓡c d)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_prod_quadrant hk).dense_compl

end ProdBoundarylessLeft

section ProdQuadrant

/-- **Sard's theorem for a product of two manifolds with corners.** -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant_prod_quadrant {d₁ d₂ : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁] [LindelofSpace M₁]
    [IsManifold (𝓡c d₁) n M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂] [LindelofSpace M₂]
    [IsManifold (𝓡c d₂) n M₂]
    {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡c d₁).prod (𝓡c d₂)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡c d₁).prod (𝓡c d₂)) J f x) :
    IsNullSet J (f '' s) := by
  induction d₁ generalizing M₁ d₂ M₂ with
  | zero =>
    have hk₀ :
        ((finrank ℝ (EuclideanSpace ℝ (Fin 0)) + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa [finrank_euclideanSpace_fin] using hk
    exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_prod_quadrant hk₀ hf hs
  | succ m₁ ih₁ =>
    induction d₂ generalizing M₂ with
    | zero =>
      have hk₀ :
          ((m₁ + 1 + finrank ℝ (EuclideanSpace ℝ (Fin 0)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
        simpa [finrank_euclideanSpace_fin] using hk
      exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant_prod hk₀ hf hs
    | succ m₂ ih₂ =>
      have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
      have : SecondCountableTopology (EuclideanQuadrant (m₁ + 1)) :=
        (𝓡c (m₁ + 1)).secondCountableTopology
      have : SecondCountableTopology M₁ :=
        ChartedSpace.secondCountable_of_lindelof (EuclideanQuadrant (m₁ + 1)) M₁
      have : SecondCountableTopology (EuclideanQuadrant (m₂ + 1)) :=
        (𝓡c (m₂ + 1)).secondCountableTopology
      have : SecondCountableTopology M₂ :=
        ChartedSpace.secondCountable_of_lindelof (EuclideanQuadrant (m₂ + 1)) M₂
      have : SecondCountableTopology ((𝓡c (m₁ + 1)).AbstractBoundary M₁) :=
        ModelWithCorners.AbstractBoundary.secondCountableTopology
          (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m₁ + 1)) hn
      have : SecondCountableTopology ((𝓡c (m₂ + 1)).AbstractBoundary M₂) :=
        ModelWithCorners.AbstractBoundary.secondCountableTopology
          (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m₂ + 1)) hn
      have hk₀ : ((finrank ℝ (EuclideanSpace ℝ (Fin (m₁ + 1)) × EuclideanSpace ℝ (Fin (m₂ + 1))) -
          finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
        simpa [finrank_euclideanSpace_fin] using hk
      have hk₁ : ((m₁ + 1 + m₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
        (Nat.cast_le.2 (by omega)).trans hk
      have hk₂ : ((m₁ + (m₂ + 1) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n :=
        (Nat.cast_le.2 (by omega)).trans hk
      refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_union_range
        (K₁ := (𝓡c (m₁ + 1)).prod (𝓡c m₂))
        (g₁ := Prod.map (id : M₁ → M₁)
          (ModelWithCorners.AbstractBoundary.point : (𝓡c (m₂ + 1)).AbstractBoundary M₂ → M₂))
        (K₂ := (𝓡c m₁).prod (𝓡c (m₂ + 1)))
        (g₂ := Prod.map
          (ModelWithCorners.AbstractBoundary.point : (𝓡c (m₁ + 1)).AbstractBoundary M₁ → M₁)
          (id : M₂ → M₂))
        hk₀ hf hs ?_
        (fun b _ ↦ (contMDiff_id.prodMap ModelWithCorners.AbstractBoundary.contMDiff_point) b)
        (fun b _ ↦ (ModelWithCorners.AbstractBoundary.contMDiff_point.prodMap contMDiff_id) b)
        (fun _ hft hst ↦ ih₂ hk₁ hft hst)
        (fun _ hft hst ↦ ih₁ hk₂ hft hst)
      rw [ModelWithCorners.boundary_prod, range_prodMap, range_prodMap, range_id, range_id,
        ModelWithCorners.AbstractBoundary.range_point
          (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m₂ + 1)) hn,
        ModelWithCorners.AbstractBoundary.range_point
          (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m₁ + 1)) hn]
      exact inter_subset_right

/-- **Sard's theorem** for a `C^k` map on a product `M₁ × M₂` of two Lindelöf manifolds with
corners. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant_prod_quadrant {d₁ d₂ : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁] [LindelofSpace M₁]
    [IsManifold (𝓡c d₁) n M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂] [LindelofSpace M₂]
    [IsManifold (𝓡c d₂) n M₂] {f : M₁ × M₂ → N}
    (hf : ContMDiff ((𝓡c d₁).prod (𝓡c d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡c d₁).prod (𝓡c d₂)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_quadrant_prod_quadrant hk
    (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on a product `M₁ × M₂` of two Lindelöf manifolds with
corners are dense when `k > d₁ + d₂ - d'` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant_prod_quadrant {d₁ d₂ : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁] [LindelofSpace M₁]
    [IsManifold (𝓡c d₁) n M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂] [LindelofSpace M₂]
    [IsManifold (𝓡c d₂) n M₂] {f : M₁ × M₂ → N}
    (hf : ContMDiff ((𝓡c d₁).prod (𝓡c d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡c d₁).prod (𝓡c d₂)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant_prod_quadrant hk).dense_compl

end ProdQuadrant

end TauCeti
