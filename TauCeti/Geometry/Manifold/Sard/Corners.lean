/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Corners.Strata.Manifold
public import TauCeti.Geometry.Manifold.Sard.Basic
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Sard's theorem for manifolds with boundary and corners

Let `f : M → N` be a `C^n` map between real manifolds modelled on finite-dimensional spaces `E` and
`E'` of dimensions `m` and `m'`, with `M` Lindelöf and `n > m - m'`, `n ≥ 1`. On a manifold with
boundary or corners, critical points can lie on the boundary or on higher-codimension corners,
where the chart-level Sard theorem for interior points
(`TauCeti.isNullSet_image_of_not_isRegularPoint_of_isInteriorPoint`) does not directly apply.

When the model range `range I` is cut out by the nonnegativity of a set of coordinates in a linear
coordinate system `L : E ≃L[ℝ] (ι → ℝ)`, i.e. `range I = {y | ∀ i ∈ S, 0 ≤ L y i}`, the manifold
`M` is partitioned into finitely many depth strata `I.depthStratum M k` (`0 ≤ k ≤ dim E`). Each
depth stratum is a boundaryless `C^n` manifold of dimension `dim E - k ≤ dim E` whose inclusion
into `M` is `C^n` (`ModelWithCorners.isManifold_depthStratum`,
`ModelWithCorners.contMDiff_subtypeVal_depthStratum`), and second countability of `M` passes to
every stratum. If a point of a stratum is not regular for `f`, it cannot be regular for the
restriction of `f` to that stratum either. Applying the boundaryless Sard theorem
(`TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt`) on each stratum — where the sharp
regularity threshold `(dim E - k) - dim E' + 1` is at most `dim E - dim E' + 1` — and taking the
finite union over `0 ≤ k ≤ dim E` shows that the critical values of `f` form a null set in `N`
(`TauCeti.IsNullSet`).

This unified argument covers the Euclidean half-space `𝓡∂ m`, the Euclidean quadrant `𝓡c m`,
products of coordinate-nonnegative models `I₁.prod I₂`, and more generally any manifold over an
arbitrary finite-dimensional real model with corners that is locally `C^n`-diffeomorphic to open
subsets of `EuclideanQuadrant (finrank ℝ E)`.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_range_eq_equiv`,
  `ContMDiff.isNullSet_image_criticalPoints_of_range_eq_equiv`,
  `ContMDiff.dense_isRegularValue_of_range_eq_equiv`: Sard's theorem and density of regular values
  at the sharp regularity `n > dim E - dim E'`, `n ≥ 1`, for any model range cut out by nonnegative
  coordinates in a linear coordinate system.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_halfSpace`,
  `ContMDiff.dense_isRegularValue_halfSpace`: Sard's theorem for manifolds with boundary modelled
  on `𝓡∂ m`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_quadrant`,
  `ContMDiff.dense_isRegularValue_quadrant`: Sard's theorem for manifolds with corners modelled on
  `𝓡c m`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_prod_of_range_eq_equiv`,
  `ContMDiff.isNullSet_image_criticalPoints_prod_of_range_eq_equiv`,
  `ContMDiff.dense_isRegularValue_prod_of_range_eq_equiv`: Sard's theorem for products of
  coordinate-nonnegative models.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_local_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_of_local_quadrant`,
  `ContMDiff.dense_isRegularValue_of_local_quadrant`: Sard's theorem for manifolds over an
  arbitrary model that are locally `C^n`-diffeomorphic to open subsets of a Euclidean quadrant.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 and Chapter 16.
* D. Joyce, *On manifolds with corners*, in *Advances in Geometric Analysis*, Adv. Lect. Math. 21,
  International Press (2012), 225–258, Section 2.
-/

public section

open Function Module Set
open scoped Manifold ContDiff

namespace TauCeti

/-- If `p` is a regular point of the composite `f ∘ g` of differentiable maps, then `g p` is a
regular point of `f`. -/
private theorem isRegularPoint_of_comp
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {G : Type*} [TopologicalSpace G] {K : ModelWithCorners 𝕜 F G}
    {P : Type*} [TopologicalSpace P] [ChartedSpace G P]
    {f : M → N} {g : P → M} {p : P}
    (h : IsRegularPoint K J (f ∘ g) p)
    (hfd : MDifferentiableAt I J f (g p)) (hgd : MDifferentiableAt K I g p) :
    IsRegularPoint I J f (g p) := by
  rw [isRegularPoint_iff] at h ⊢
  rw [mfderiv_comp p hfd hgd, ContinuousLinearMap.coe_comp] at h
  exact h.of_comp

/-! ### Coordinate-nonnegative models -/

section CoordModel

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with corners modelled on nonnegative coordinate cones.** Let `M`
be a Lindelöf `C^n` manifold whose model range is cut out by nonnegative coordinates under a linear
coordinate equivalence `L : E ≃L[ℝ] (ι → ℝ)`. If `n > dim E - dim E'` and `n ≥ 1`, and `f` is `C^n`
at every point of a set `s` of non-regular points, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_range_eq_equiv
    {ι : Type*} [Finite ι] (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  have hn0 : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : FiniteDimensional ℝ E := L.symm.toLinearEquiv.finiteDimensional
  have : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn0)
  have : IsManifold J 1 N := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn0)
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_lindelof H M
  have hcov : f '' s ⊆ ⋃ k ≤ finrank ℝ E,
      (f ∘ (Subtype.val : I.depthStratum M k → M)) '' (Subtype.val ⁻¹' s) := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_iUnion₂.2 ⟨I.depth x, I.depth_le_finrank x,
      ⟨⟨x, ModelWithCorners.mem_depthStratum.2 rfl⟩, hx, rfl⟩⟩
  refine (IsNullSet.biUnion (Set.finite_le_nat _).countable fun k _ ↦ ?_).mono hcov
  let _ := I.depthStratumChartedSpace M L hI k
  let _ := I.isManifold_depthStratum (M := M) L hI hn0 k
  have hk' :
      ((finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤
        n := by
    refine le_trans ?_ hk
    exact_mod_cast (by rw [finrank_euclideanSpace_fin]; omega :
      finrank ℝ (EuclideanSpace ℝ (Fin (finrank ℝ E - k))) - finrank ℝ E' + 1 ≤
        finrank ℝ E - finrank ℝ E' + 1)
  have hval := I.contMDiff_subtypeVal_depthStratum (M := M) L hI hn0 k
  refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
    (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin (finrank ℝ E - k)))) hk'
    (fun p hp ↦ (hf p.1 hp).comp p (hval p)) fun p hp hreg ↦ ?_
  exact hs p.1 hp (isRegularPoint_of_comp hreg ((hf p.1 hp).mdifferentiableAt hn0)
    ((hval p).mdifferentiableAt hn0))

/-- **Sard's theorem for manifolds with corners modelled on nonnegative coordinate cones:** the
critical values of a `C^n` map (`n > dim E - dim E'`, `n ≥ 1`) form a null set. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_range_eq_equiv
    {ι : Type*} [Finite ι] (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_range_eq_equiv L hI hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^n` map (`n > dim E - dim E'`, `n ≥ 1`) from a Lindelöf manifold
whose model range is cut out by nonnegative coordinates are dense. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_range_eq_equiv
    {ι : Type*} [Finite ι] (L : E ≃L[ℝ] (ι → ℝ)) {S : Set ι}
    (hI : range I = {y | ∀ i ∈ S, 0 ≤ L y i})
    (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_of_range_eq_equiv L hI hk).dense_compl

end CoordModel

/-! ### Manifolds with boundary (`𝓡∂ m`) -/

section HalfSpace

variable {m : ℕ} [NeZero m]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace m) M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold (𝓡∂ m) n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with boundary:** if `M` is a Lindelöf `C^n` manifold modelled on
`𝓡∂ m`, `n > m - dim E'` and `n ≥ 1`, and `f` is `C^n` on a set `s` of non-regular points (boundary
points included), then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_halfSpace
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡∂ m) J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡∂ m) J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_range_eq_equiv
    (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearEquiv
    (ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq_equiv m)
    (by simpa [finrank_euclideanSpace_fin] using hk) hf hs

/-- **Sard's theorem for manifolds with boundary:** the critical values of a `C^n` map from a
Lindelöf manifold modelled on `𝓡∂ m` (`n > m - dim E'`, `n ≥ 1`), boundary points included, form a
null set. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace
    (hf : ContMDiff (𝓡∂ m) J n f)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡∂ m) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^n` map from a Lindelöf manifold modelled on `𝓡∂ m`
(`n > m - dim E'`, `n ≥ 1`) are dense. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace
    (hf : ContMDiff (𝓡∂ m) J n f)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (𝓡∂ m) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace hk).dense_compl

end HalfSpace

/-! ### Manifolds with corners (`𝓡c m`) -/

section Quadrant

variable {m : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant m) M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold (𝓡c m) n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with corners modelled on `𝓡c m`:** if `M` is a Lindelöf `C^n`
manifold modelled on `𝓡c m`, `n > m - dim E'` and `n ≥ 1`, and `f` is `C^n` on a set `s` of
non-regular points (corner points included), then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_quadrant
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡c m) J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡c m) J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_range_eq_equiv
    (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearEquiv
    (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq_equiv m)
    (by simpa [finrank_euclideanSpace_fin] using hk) hf hs

/-- **Sard's theorem for manifolds with corners modelled on `𝓡c m`:** the critical values of a `C^n`
map (`n > m - dim E'`, `n ≥ 1`), corner points included, form a null set. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant
    (hf : ContMDiff (𝓡c m) J n f)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡c m) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_quadrant hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^n` map from a Lindelöf manifold modelled on `𝓡c m`
(`n > m - dim E'`, `n ≥ 1`) are dense. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant
    (hf : ContMDiff (𝓡c m) J n f)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (𝓡c m) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant hk).dense_compl

end Quadrant

/-! ### Products of coordinate-nonnegative models -/

section Prod

variable {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
  {H₂ : Type*} [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (ModelProd H₁ H₂) M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold (I₁.prod I₂) n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for products of coordinate-nonnegative models:** if `I₁` and `I₂` have ranges
cut out by nonnegative coordinates under `L₁` and `L₂`, then Sard's theorem holds for `C^n` maps
from any Lindelöf manifold modelled on `I₁.prod I₂` at the sharp regularity
`n > dim E₁ + dim E₂ - dim E'`, `n ≥ 1`. -/
theorem isNullSet_image_of_not_isRegularPoint_prod_of_range_eq_equiv
    {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂]
    (L₁ : E₁ ≃L[ℝ] (ι₁ → ℝ)) {S₁ : Set ι₁} (hI₁ : range I₁ = {y | ∀ i ∈ S₁, 0 ≤ L₁ y i})
    (L₂ : E₂ ≃L[ℝ] (ι₂ → ℝ)) {S₂ : Set ι₂} (hI₂ : range I₂ = {y | ∀ j ∈ S₂, 0 ≤ L₂ y j})
    (hk : ((finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod I₂) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod I₂) J f x) :
    IsNullSet J (f '' s) := by
  have : FiniteDimensional ℝ E₁ := L₁.symm.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ E₂ := L₂.symm.toLinearEquiv.finiteDimensional
  exact isNullSet_image_of_not_isRegularPoint_of_range_eq_equiv
    (prodCoordEquiv L₁ L₂)
    (ModelWithCorners.range_prod_eq_of_range_eq_equiv hI₁ hI₂)
    (by simpa [Module.finrank_prod] using hk) hf hs

/-- The critical values of a `C^n` map from a Lindelöf manifold modelled on a product `I₁.prod I₂`
of coordinate-nonnegative models form a null set when `n > dim E₁ + dim E₂ - dim E'` and
`n ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_prod_of_range_eq_equiv
    {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂]
    (L₁ : E₁ ≃L[ℝ] (ι₁ → ℝ)) {S₁ : Set ι₁} (hI₁ : range I₁ = {y | ∀ i ∈ S₁, 0 ≤ L₁ y i})
    (L₂ : E₂ ≃L[ℝ] (ι₂ → ℝ)) {S₂ : Set ι₂} (hI₂ : range I₂ = {y | ∀ j ∈ S₂, 0 ≤ L₂ y j})
    (hf : ContMDiff (I₁.prod I₂) J n f)
    (hk : ((finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (I₁.prod I₂) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_prod_of_range_eq_equiv L₁ hI₁ L₂ hI₂ hk
    (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^n` map from a Lindelöf manifold modelled on a product `I₁.prod I₂`
of coordinate-nonnegative models are dense when `n > dim E₁ + dim E₂ - dim E'` and `n ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_prod_of_range_eq_equiv
    {ι₁ ι₂ : Type*} [Finite ι₁] [Finite ι₂]
    (L₁ : E₁ ≃L[ℝ] (ι₁ → ℝ)) {S₁ : Set ι₁} (hI₁ : range I₁ = {y | ∀ i ∈ S₁, 0 ≤ L₁ y i})
    (L₂ : E₂ ≃L[ℝ] (ι₂ → ℝ)) {S₂ : Set ι₂} (hI₂ : range I₂ = {y | ∀ j ∈ S₂, 0 ≤ L₂ y j})
    (hf : ContMDiff (I₁.prod I₂) J n f)
    (hk : ((finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (I₁.prod I₂) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_prod_of_range_eq_equiv L₁ hI₁ L₂ hI₂ hk).dense_compl

end Prod

/-! ### Manifolds locally diffeomorphic to Euclidean quadrants -/

section LocalQuadrant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds locally modelled on Euclidean quadrants:** if `M` is a Lindelöf
`C^n` manifold over an arbitrary finite-dimensional real model with corners `I` such that every
point of `s` has an open neighbourhood `C^n`-diffeomorphic to an open subset of
`EuclideanQuadrant (finrank ℝ E)`, then for `n > dim E - dim E'` and `n ≥ 1` the image `f '' s` of
non-regular points where `f` is `C^n` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_local_quadrant
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hloc : ∀ x ∈ s, ∃ (U : TopologicalSpace.Opens M)
      (V : TopologicalSpace.Opens (EuclideanQuadrant (finrank ℝ E))),
      x ∈ U ∧ Nonempty (U ≃ₘ^n⟮I, 𝓡c (finrank ℝ E)⟯ V))
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  have hn0 : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : IsManifold I 1 M := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn0)
  have : IsManifold J 1 N := IsManifold.of_le (ENat.one_le_iff_ne_zero_withTop.2 hn0)
  have : SecondCountableTopology H := I.secondCountableTopology
  have : SecondCountableTopology M := ChartedSpace.secondCountable_of_lindelof H M
  choose U V hxU hΦ using fun x : s ↦ hloc x.1 x.2
  obtain ⟨t, ht, hcovU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : s ↦ (U x : Set M)) (fun x ↦ (U x).isOpen)
  have hcov : f '' s ⊆ ⋃ x ∈ t, f '' (s ∩ (U x : Set M)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyU : y ∈ ⋃ x : s, (U x : Set M) := mem_iUnion.2 ⟨⟨y, hy⟩, hxU ⟨y, hy⟩⟩
    rw [← hcovU] at hyU
    obtain ⟨x, hxt, hyUx⟩ := mem_iUnion₂.1 hyU
    exact mem_biUnion hxt ⟨y, ⟨hy, hyUx⟩, rfl⟩
  refine (IsNullSet.biUnion ht fun x _ ↦ ?_).mono hcov
  obtain ⟨Φ⟩ := hΦ x
  have himg : f '' (s ∩ (U x : Set M)) =
      (f ∘ (Subtype.val : U x → M) ∘ Φ.symm) '' (Φ '' (Subtype.val ⁻¹' s)) := by
    ext y
    constructor
    · rintro ⟨m, ⟨hms, hmU⟩, rfl⟩
      exact ⟨Φ ⟨m, hmU⟩, ⟨⟨m, hmU⟩, hms, rfl⟩, by simp⟩
    · rintro ⟨v, ⟨u, hus, rfl⟩, rfl⟩
      exact ⟨u.1, ⟨hus, u.2⟩, by simp⟩
  rw [himg]
  have : SecondCountableTopology (EuclideanQuadrant (finrank ℝ E)) :=
    (𝓡c (finrank ℝ E)).secondCountableTopology
  refine isNullSet_image_of_not_isRegularPoint_quadrant hk ?_ ?_
  · rintro _ ⟨u, hus, rfl⟩
    have hcomp : ContMDiffAt (𝓡c (finrank ℝ E)) I n ((Subtype.val : U x → M) ∘ Φ.symm) (Φ u) :=
      (contMDiff_subtype_val (Φ.symm (Φ u))).comp (Φ u) (Φ.symm.contMDiff (Φ u))
    have hfu : ContMDiffAt I J n f (((Subtype.val : U x → M) ∘ Φ.symm) (Φ u)) := by
      simpa using hf u.1 hus
    exact hfu.comp (Φ u) hcomp
  · rintro _ ⟨u, hus, rfl⟩ hreg
    have hcomp : MDifferentiableAt (𝓡c (finrank ℝ E)) I ((Subtype.val : U x → M) ∘ Φ.symm) (Φ u) :=
      ((contMDiff_subtype_val (Φ.symm (Φ u))).comp (Φ u)
        (Φ.symm.contMDiff (Φ u))).mdifferentiableAt hn0
    have hfd : MDifferentiableAt I J f (((Subtype.val : U x → M) ∘ Φ.symm) (Φ u)) := by
      simpa using (hf u.1 hus).mdifferentiableAt hn0
    have hreg' : IsRegularPoint I J f u.1 := by
      simpa using isRegularPoint_of_comp hreg hfd hcomp
    exact hs u.1 hus hreg'

/-- The critical values of a `C^n` map (`n > dim E - dim E'`, `n ≥ 1`) from a Lindelöf manifold
locally `C^n`-diffeomorphic to open subsets of `EuclideanQuadrant (finrank ℝ E)` form a null
set. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_local_quadrant
    (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hloc : ∀ x : M, ∃ (U : TopologicalSpace.Opens M)
      (V : TopologicalSpace.Opens (EuclideanQuadrant (finrank ℝ E))),
      x ∈ U ∧ Nonempty (U ≃ₘ^n⟮I, 𝓡c (finrank ℝ E)⟯ V)) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_local_quadrant hk (fun x _ ↦ hloc x)
    (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^n` map (`n > dim E - dim E'`, `n ≥ 1`) from a Lindelöf manifold
locally `C^n`-diffeomorphic to open subsets of `EuclideanQuadrant (finrank ℝ E)` are dense. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_local_quadrant
    (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hloc : ∀ x : M, ∃ (U : TopologicalSpace.Opens M)
      (V : TopologicalSpace.Opens (EuclideanQuadrant (finrank ℝ E))),
      x ∈ U ∧ Nonempty (U ≃ₘ^n⟮I, 𝓡c (finrank ℝ E)⟯ V)) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_of_local_quadrant hk hloc).dense_compl

end LocalQuadrant

end TauCeti
