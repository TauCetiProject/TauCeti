/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Corners.AbstractBoundary.Manifold
public import TauCeti.Geometry.Manifold.Sard.Basic
import TauCeti.Geometry.Manifold.ChartedSpace

/-!
# Sard's theorem for manifolds with boundary, quadrant corners, and their products

Let `f : M → N` be a map from a Lindelöf real manifold `M` of dimension `m` to a real manifold `N`
of dimension `n'`, where `N` may have arbitrary boundary or corners. When `M` has boundary or
corners, the coordinate representative of `f` at a boundary point is smooth only within the model
range, so the flat Morse–Sard theorem cannot be applied directly in ambient charts. Instead, a
point of `M` that is critical for `f` (meaning `mfderiv` is not surjective) remains critical after
precomposing with any smooth map into `M` (`TauCeti.IsRegularPoint.of_comp`). Covering the critical
set, or the boundary of `M` via `TauCeti.isNullSet_image_iff_inter_boundary`, by countably many
maps from boundaryless Lindelöf manifolds therefore reduces Sard's theorem to the boundaryless case
in `TauCeti.Geometry.Manifold.Sard.Basic`, at the sharp regularity `C^k` with `k > m - n'` and
`k ≥ 1`.

This file establishes the general countable-cover reduction and instantiates it for:

* manifolds with boundary modelled on `EuclideanHalfSpace d` (`𝓡∂ d`, `d ≥ 1`), using the boundary
  manifold `TauCeti.boundaryChartedSpace`;
* manifolds with corners modelled on `EuclideanQuadrant d` (`𝓡c d`, any `d : ℕ`), using the
  abstract boundary `ModelWithCorners.AbstractBoundary` to peel off one corner depth at a time;
* products of boundaryless manifolds, manifolds with boundary, and manifolds with quadrant corners,
  in all combinations of `ModelWithCorners.prod`.

In every case we record the pointwise-on-`s` theorem, the global critical-values theorem
`ContMDiff.isNullSet_image_criticalPoints_*`, and density of regular values
`ContMDiff.dense_isRegularValue_*`.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_subset_iUnion_range`: if `s` is covered by the
  ranges of countably many `C^k` maps from boundaryless Lindelöf manifolds of suitable dimensions,
  and `f` is `C^k` and non-regular on `s`, then `f '' s` is null.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_halfSpace`, and
  `ContMDiff.dense_isRegularValue_halfSpace`: Sard's theorem and density of regular values on
  manifolds with boundary.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_quadrant`, and
  `ContMDiff.dense_isRegularValue_quadrant`: Sard's theorem and density of regular values on
  manifolds with quadrant corners.
* `ContMDiff.isNullSet_image_criticalPoints_prod_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_prod_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_quadrant_prod_quadrant` (together with their swapped
  variants, pointwise-on-`s` forms, and regular-value density corollaries): Sard's theorem on
  products of boundaryless, half-space, and quadrant manifolds.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 (Sard's theorem for manifolds with or without boundary) and
  Chapter 16 (manifolds with corners).
-/

public section

open Function Module Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-! ### Countable covers by boundaryless manifolds -/

section Cover

omit [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] in
/-- Precomposing a map `f` that is `C^n` (`n ≠ 0`) and non-regular at `g p` with a map `g` that is
`C^n` at `p` produces a composite `f ∘ g` that is `C^n` and non-regular at `p`. -/
private theorem contMDiffAt_and_not_isRegularPoint_comp {n : ℕ∞ω} (hn : n ≠ 0)
    {E H M E'' H'' P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
    [TopologicalSpace P] [ChartedSpace H'' P]
    {f : M → N} {g : P → M} {p : P}
    (hf : ContMDiffAt I J n f (g p)) (hreg : ¬ IsRegularPoint I J f (g p))
    (hg : ContMDiffAt K I n g p) :
    ContMDiffAt K J n (f ∘ g) p ∧ ¬ IsRegularPoint K J (f ∘ g) p :=
  ⟨hf.comp p hg, fun h ↦ hreg (h.of_comp (hf.mdifferentiableAt hn) (hg.mdifferentiableAt hn))⟩

omit [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E'] in
/-- Pulling `s ∩ t` back along a `C^n` (`n ≠ 0`) map `g : P → M` with `range g = t` rewrites
`f '' (s ∩ t)` as `(f ∘ g) '' (g ⁻¹' s)` and transfers `C^n` regularity and non-regularity from
`f` on `s` to `f ∘ g` on `g ⁻¹' s`. -/
private theorem image_inter_eq_and_not_isRegularPoint_comp {n : ℕ∞ω} (hn : n ≠ 0)
    {E H M E'' H'' P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup E''] [NormedSpace ℝ E'']
    [TopologicalSpace H''] {K : ModelWithCorners ℝ E'' H''}
    [TopologicalSpace P] [ChartedSpace H'' P]
    {f : M → N} {s t : Set M} {g : P → M} (hrange : range g = t)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (hg : ContMDiff K I n g) :
    f '' (s ∩ t) = (f ∘ g) '' (g ⁻¹' s) ∧
      (∀ q ∈ g ⁻¹' s, ContMDiffAt K J n (f ∘ g) q) ∧
      (∀ q ∈ g ⁻¹' s, ¬ IsRegularPoint K J (f ∘ g) q) := by
  refine ⟨by rw [← hrange, ← image_preimage_eq_inter_range, ← image_comp],
    fun q hq ↦ (contMDiffAt_and_not_isRegularPoint_comp hn (hf _ hq) (hs _ hq) (hg q)).1,
    fun q hq ↦ (contMDiffAt_and_not_isRegularPoint_comp hn (hf _ hq) (hs _ hq) (hg q)).2⟩

/-- **Sard's theorem along a countable family of boundaryless strata.** Let `s` be a set of
non-regular points of `f : M → N` at which `f` is `C^k`, covered by the ranges of countably many
maps `g i : P i → M` from boundaryless Lindelöf `C^k` manifolds `P i` of dimensions `mᵢ`, each `C^k`
at the preimages of `s`. If `k > mᵢ - dim N` and `k ≥ 1` for every `i`, then `f '' s` is null in
`N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_subset_iUnion_range
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {ι : Sort*} [Countable ι]
    {Eᵢ : ι → Type*} [∀ i, NormedAddCommGroup (Eᵢ i)] [∀ i, NormedSpace ℝ (Eᵢ i)]
    [∀ i, FiniteDimensional ℝ (Eᵢ i)]
    {Hᵢ : ι → Type*} [∀ i, TopologicalSpace (Hᵢ i)] {K : ∀ i, ModelWithCorners ℝ (Eᵢ i) (Hᵢ i)}
    {P : ι → Type*} [∀ i, TopologicalSpace (P i)] [∀ i, ChartedSpace (Hᵢ i) (P i)]
    [∀ i, LindelofSpace (P i)] [∀ i, BoundarylessManifold (K i) (P i)]
    {n : ℕ∞ω} [∀ i, IsManifold (K i) n (P i)] [IsManifold J n N]
    {f : M → N} {s : Set M} {g : ∀ i, P i → M}
    (hk : ∀ i, ((finrank ℝ (Eᵢ i) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hcov : s ⊆ ⋃ i, range (g i))
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (hg : ∀ i, ∀ p ∈ g i ⁻¹' s, ContMDiffAt (K i) I n (g i) p) :
    IsNullSet J (f '' s) := by
  refine (IsNullSet.iUnion fun i ↦ ?_).mono (t := ⋃ i, (f ∘ g i) '' (g i ⁻¹' s)) ?_
  · have hn : n ≠ 0 := fun h ↦ by have := hk i; simp [h] at this
    have key : ∀ p ∈ g i ⁻¹' s,
        ContMDiffAt (K i) J n (f ∘ g i) p ∧ ¬ IsRegularPoint (K i) J (f ∘ g i) p :=
      fun p hp ↦ contMDiffAt_and_not_isRegularPoint_comp hn (hf _ hp) (hs _ hp) (hg i p hp)
    exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt (hk i)
      (fun p hp ↦ (key p hp).1) fun p hp ↦ (key p hp).2
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, p, rfl⟩ := mem_iUnion.1 (hcov hx)
    exact mem_iUnion.2 ⟨i, p, hx, rfl⟩

end Cover

/-! ### Manifolds with boundary -/

section HalfSpace

variable {d : ℕ} [NeZero d]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M] [LindelofSpace M]
  {n : ℕ∞ω} [IsManifold (𝓡∂ d) n M] [IsManifold J n N] {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with boundary.** Let `M` be a Lindelöf manifold modelled on the
`d`-dimensional half-space `EuclideanHalfSpace d` and `N` a manifold modelled on a space `E'` of
dimension `n'`, possibly with boundary or corners. If `f` is `C^k` at every point of `s` with
`k > d - n'` and `k ≥ 1`, and no point of `s` is regular, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_halfSpace
    (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡∂ d) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡∂ d) J f x) :
    IsNullSet J (f '' s) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : IsManifold (𝓡∂ (m + 1)) 1 M := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) n ↥((𝓡∂ (m + 1)).boundary M) :=
    isManifold_boundary M hn
  have : SecondCountableTopology (EuclideanHalfSpace (m + 1)) :=
    (𝓡∂ (m + 1)).secondCountableTopology
  have : SecondCountableTopology M :=
    ChartedSpace.secondCountable_of_lindelof (EuclideanHalfSpace (m + 1)) M
  have : SecondCountableTopology ↥((𝓡∂ (m + 1)).boundary M) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hk_int :
      ((finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
    simpa only [finrank_euclideanSpace_fin] using hk
  rw [isNullSet_image_iff_inter_boundary hk_int (fun x hx _ ↦ hf x hx) (fun x hx _ ↦ hs x hx)]
  obtain ⟨himg, hfg, hsfg⟩ := image_inter_eq_and_not_isRegularPoint_comp hn
    (Subtype.range_coe (s := (𝓡∂ (m + 1)).boundary M)) hf hs
    (isSmoothEmbedding_subtypeVal_boundary (n := m) (k := n) M hn).contMDiff
  rw [himg]
  exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
    (le_trans (Nat.cast_le.2 (by rw [finrank_euclideanSpace_fin]; omega)) hk) hfg hsfg

/-- **Sard's theorem for manifolds with boundary.** The critical values of a `C^k` map from a
Lindelöf `d`-manifold with boundary to a manifold of dimension `n'` form a null set when
`k > d - n'` and `k ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace
    (hf : ContMDiff (𝓡∂ d) J n f) (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡∂ d) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map from a Lindelöf `d`-manifold with boundary to a manifold of
dimension `n'` are dense when `k > d - n'` and `k ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace
    (hf : ContMDiff (𝓡∂ d) J n f) (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (𝓡∂ d) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace hk).dense_compl

end HalfSpace

/-! ### Manifolds with quadrant corners -/

section Quadrant

variable {d : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M] [LindelofSpace M]
  {n : ℕ∞ω} [IsManifold (𝓡c d) n M] [IsManifold J n N] {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with quadrant corners.** Let `M` be a Lindelöf manifold modelled
on the `d`-dimensional quadrant `EuclideanQuadrant d` and `N` a manifold modelled on a space `E'`
of dimension `n'`, possibly with boundary or corners. If `f` is `C^k` at every point of `s` with
`k > d - n'` and `k ≥ 1`, and no point of `s` is regular, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_quadrant
    (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡c d) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡c d) J f x) :
    IsNullSet J (f '' s) := by
  induction d generalizing M with
  | zero =>
    have : (𝓡c 0).Boundaryless := ⟨by simp [range_modelWithCornersEuclideanQuadrant]⟩
    have hk₀ : ((finrank ℝ (EuclideanSpace ℝ (Fin 0)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa only [finrank_euclideanSpace_fin] using hk
    exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk₀ hf hs
  | succ m ih =>
    have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
    have hk_int :
        ((finrank ℝ (EuclideanSpace ℝ (Fin (m + 1))) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa only [finrank_euclideanSpace_fin] using hk
    rw [isNullSet_image_iff_inter_boundary hk_int (fun x hx _ ↦ hf x hx) (fun x hx _ ↦ hs x hx)]
    have : SecondCountableTopology ((𝓡c (m + 1)).AbstractBoundary M) :=
      ModelWithCorners.AbstractBoundary.secondCountableTopology
        (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn
    obtain ⟨himg, hfg, hsfg⟩ := image_inter_eq_and_not_isRegularPoint_comp hn
      (ModelWithCorners.AbstractBoundary.range_point
        (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn)
      hf hs ModelWithCorners.AbstractBoundary.contMDiff_point
    rw [himg]
    exact ih (le_trans (Nat.cast_le.2 (by omega)) hk) hfg hsfg

/-- **Sard's theorem for manifolds with quadrant corners.** The critical values of a `C^k` map from
a Lindelöf `d`-manifold with quadrant corners to a manifold of dimension `n'` form a null set when
`k > d - n'` and `k ≥ 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant
    (hf : ContMDiff (𝓡c d) J n f) (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡c d) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_quadrant hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map from a Lindelöf `d`-manifold with quadrant corners to a
manifold of dimension `n'` are dense when `k > d - n'` and `k ≥ 1`, in particular when the map is
smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant
    (hf : ContMDiff (𝓡c d) J n f) (hk : ((d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (𝓡c d) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant hk).dense_compl

end Quadrant

/-! ### Products of boundaryless, half-space, and quadrant manifolds -/

section Product

/-- If a nonempty product of charted spaces over second-countable models is Lindelöf, both factors
are second countable. -/
private theorem secondCountableTopology_of_lindelof_prod
    (H₁ M₁ H₂ M₂ : Type*)
    [TopologicalSpace H₁] [SecondCountableTopology H₁] [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [TopologicalSpace H₂] [SecondCountableTopology H₂] [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [LindelofSpace (M₁ × M₂)] [Nonempty (M₁ × M₂)] :
    SecondCountableTopology M₁ ∧ SecondCountableTopology M₂ := by
  obtain ⟨⟨p₀, q₀⟩⟩ := ‹Nonempty (M₁ × M₂)›
  have : Nonempty M₁ := ⟨p₀⟩
  have : Nonempty M₂ := ⟨q₀⟩
  have : LindelofSpace M₁ := .of_continuous_surjective
    (continuous_fst : Continuous (Prod.fst : M₁ × M₂ → M₁)) Prod.fst_surjective
  have : LindelofSpace M₂ := .of_continuous_surjective
    (continuous_snd : Continuous (Prod.snd : M₁ × M₂ → M₂)) Prod.snd_surjective
  exact ⟨ChartedSpace.secondCountable_of_lindelof H₁ M₁,
    ChartedSpace.secondCountable_of_lindelof H₂ M₂⟩

/-- On a Lindelöf product manifold `M₁ × M₂`, nullity of `f '' s` for `C^n` non-regular `f`
reduces to nullity along the two boundary faces `univ ×ˢ I₂.boundary M₂` and
`I₁.boundary M₁ ×ˢ univ`, with both factors second countable. -/
private theorem isNullSet_image_prod_of_inter_boundary
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
    [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold I₁ n M₁] [IsManifold I₂ n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hk : ((finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod I₂) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod I₂) J f x)
    (hb₂ : ∀ [SecondCountableTopology M₁] [SecondCountableTopology M₂],
      n ≠ 0 → IsNullSet J (f '' (s ∩ (univ : Set M₁) ×ˢ I₂.boundary M₂)))
    (hb₁ : ∀ [SecondCountableTopology M₁] [SecondCountableTopology M₂],
      n ≠ 0 → IsNullSet J (f '' (s ∩ I₁.boundary M₁ ×ˢ (univ : Set M₂)))) :
    IsNullSet J (f '' s) := by
  rcases isEmpty_or_nonempty (M₁ × M₂) with hemp | hne
  · rw [Set.eq_empty_of_isEmpty s, image_empty]
    exact (isNullSet_iff J ∅).2 fun _ _ _ ↦ by simp
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : SecondCountableTopology H₁ := I₁.secondCountableTopology
  have : SecondCountableTopology H₂ := I₂.secondCountableTopology
  obtain ⟨_, _⟩ := secondCountableTopology_of_lindelof_prod H₁ M₁ H₂ M₂
  have hk_int : ((finrank ℝ (E₁ × E₂) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
    simpa only [Module.finrank_prod] using hk
  rw [isNullSet_image_iff_inter_boundary hk_int (fun x hx _ ↦ hf x hx) (fun x hx _ ↦ hs x hx),
    ModelWithCorners.boundary_prod, inter_union_distrib_left, image_union]
  exact (hb₂ hn).union (hb₁ hn)

omit [FiniteDimensional ℝ E'] in
/-- On a product whose left factor is boundaryless, the left-boundary slice is empty, hence its
image is null. -/
private theorem isNullSet_image_inter_boundary_of_boundaryless_left
    {E₁ H₁ P M : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {K : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace P] [ChartedSpace H₁ P]
    [BoundarylessManifold K P] {f : P × M → N} {s : Set (P × M)} :
    IsNullSet J (f '' (s ∩ K.boundary P ×ˢ (univ : Set M))) := by
  rw [ModelWithCorners.Boundaryless.boundary_eq_empty, empty_prod, inter_empty, image_empty]
  exact (isNullSet_iff J ∅).2 fun _ _ _ ↦ by simp

omit [FiniteDimensional ℝ E'] in
/-- Swapping factors reduces nullity of `f '' s` on `M₁ × M₂` to nullity of
`(f ∘ Prod.swap) '' (Prod.swap ⁻¹' s)` on the Lindelöf product `M₂ × M₁`. -/
private theorem isNullSet_image_of_swap {n : ℕ∞ω} (hn : n ≠ 0)
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [LindelofSpace (M₁ × M₂)] {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod I₂) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod I₂) J f x)
    (hswap : ∀ [LindelofSpace (M₂ × M₁)],
      (∀ q ∈ Prod.swap ⁻¹' s, ContMDiffAt (I₂.prod I₁) J n (f ∘ Prod.swap) q) →
      (∀ q ∈ Prod.swap ⁻¹' s, ¬ IsRegularPoint (I₂.prod I₁) J (f ∘ Prod.swap) q) →
      IsNullSet J ((f ∘ Prod.swap) '' (Prod.swap ⁻¹' s))) :
    IsNullSet J (f '' s) := by
  have : LindelofSpace (M₂ × M₁) :=
    .of_continuous_surjective continuous_swap Prod.swap_surjective
  obtain ⟨himg, hfg, hsfg⟩ := image_inter_eq_and_not_isRegularPoint_comp hn
    (Prod.swap_surjective.range_eq : range (Prod.swap : M₂ × M₁ → _) = _) hf hs
    (contMDiff_snd.prodMk contMDiff_fst : ContMDiff (I₂.prod I₁) (I₁.prod I₂) n _)
  rw [← inter_univ s, himg]
  exact hswap hfg hsfg

omit [FiniteDimensional ℝ E'] in
/-- Swapping the factors of `M₁ × M₂` rewrites the left-boundary slice
`s ∩ I₁.boundary M₁ ×ˢ univ` as the right-boundary slice
`(Prod.swap ⁻¹' s) ∩ univ ×ˢ I₁.boundary M₁` for `f ∘ Prod.swap`. -/
private theorem isNullSet_image_inter_prod_univ_of_swap {n : ℕ∞ω} (hn : n ≠ 0)
    {E₁ H₁ M₁ E₂ H₂ M₂ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod I₂) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod I₂) J f x)
    (hswap :
      (∀ q ∈ Prod.swap ⁻¹' s, ContMDiffAt (I₂.prod I₁) J n (f ∘ Prod.swap) q) →
      (∀ q ∈ Prod.swap ⁻¹' s, ¬ IsRegularPoint (I₂.prod I₁) J (f ∘ Prod.swap) q) →
      IsNullSet J
        ((f ∘ Prod.swap) '' (Prod.swap ⁻¹' s ∩ (univ : Set M₂) ×ˢ I₁.boundary M₁))) :
    IsNullSet J (f '' (s ∩ I₁.boundary M₁ ×ˢ (univ : Set M₂))) := by
  have hg : ContMDiff (I₂.prod I₁) (I₁.prod I₂) n (Prod.swap : M₂ × M₁ → M₁ × M₂) :=
    contMDiff_snd.prodMk contMDiff_fst
  have hswap_set : Prod.swap '' (Prod.swap ⁻¹' s ∩ (univ : Set M₂) ×ˢ I₁.boundary M₁) =
      s ∩ I₁.boundary M₁ ×ˢ (univ : Set M₂) := by
    ext ⟨x₁, x₂⟩
    exact ⟨fun ⟨⟨_, _⟩, ⟨hys, _, hy₁⟩, h⟩ ↦ by cases h; exact ⟨hys, hy₁, trivial⟩,
      fun ⟨hxs, hx₁, _⟩ ↦ ⟨(x₂, x₁), ⟨hxs, trivial, hx₁⟩, rfl⟩⟩
  rw [← hswap_set, ← image_comp]
  exact hswap
    (fun q hq ↦ (contMDiffAt_and_not_isRegularPoint_comp hn (hf _ hq) (hs _ hq) (hg q)).1)
    (fun q hq ↦ (contMDiffAt_and_not_isRegularPoint_comp hn (hf _ hq) (hs _ hq) (hg q)).2)

omit [FiniteDimensional ℝ E'] in
/-- Given a `C^n` (`n ≠ 0`) parametrization `g : B → M₂` of `I₂.boundary M₂`, nullity of
`f '' (s ∩ univ ×ˢ I₂.boundary M₂)` reduces to nullity of
`(f ∘ Prod.map id g) '' (Prod.map id g ⁻¹' s)` on `M₁ × B`. -/
private theorem isNullSet_image_inter_univ_prod_of_range_eq {n : ℕ∞ω} (hn : n ≠ 0)
    {E₁ H₁ M₁ E₂ H₂ M₂ E₃ H₃ B : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [TopologicalSpace H₃]
    {I₃ : ModelWithCorners ℝ E₃ H₃} [TopologicalSpace B] [ChartedSpace H₃ B]
    {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)} {g : B → M₂}
    (hrange : range g = I₂.boundary M₂) (hg : ContMDiff I₃ I₂ n g)
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod I₂) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod I₂) J f x)
    (hbdry :
      (∀ q ∈ Prod.map id g ⁻¹' s, ContMDiffAt (I₁.prod I₃) J n (f ∘ Prod.map id g) q) →
      (∀ q ∈ Prod.map id g ⁻¹' s, ¬ IsRegularPoint (I₁.prod I₃) J (f ∘ Prod.map id g) q) →
      IsNullSet J ((f ∘ Prod.map id g) '' (Prod.map id g ⁻¹' s))) :
    IsNullSet J (f '' (s ∩ (univ : Set M₁) ×ˢ I₂.boundary M₂)) := by
  have hrange' : range (Prod.map (id : M₁ → M₁) g) = (univ : Set M₁) ×ˢ I₂.boundary M₂ := by
    rw [Set.range_prodMap, range_id, hrange]
  obtain ⟨himg, hfg, hsfg⟩ := image_inter_eq_and_not_isRegularPoint_comp hn hrange' hf hs
    (contMDiff_id.prodMap hg)
  rw [himg]
  exact hbdry hfg hsfg

omit [FiniteDimensional ℝ E'] in
/-- On a product whose right factor is a second-countable half-space manifold `M₂`, nullity along
`univ ×ˢ (𝓡∂ (m + 1)).boundary M₂` reduces to nullity on `M₁ × ↥((𝓡∂ (m + 1)).boundary M₂)`. -/
private theorem isNullSet_image_inter_univ_prod_boundary_halfSpace {n : ℕ∞ω} (hn : n ≠ 0)
    {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    {m : ℕ} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace (m + 1)) M₂]
    [SecondCountableTopology M₂] [IsManifold (𝓡∂ (m + 1)) n M₂]
    {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod (𝓡∂ (m + 1))) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod (𝓡∂ (m + 1))) J f x)
    (hbdry : ∀ [IsManifold (𝓡∂ (m + 1)) 1 M₂]
      [SecondCountableTopology ↥((𝓡∂ (m + 1)).boundary M₂)]
      [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) n ↥((𝓡∂ (m + 1)).boundary M₂)]
      {g : M₁ × ↥((𝓡∂ (m + 1)).boundary M₂) → N}
      {t : Set (M₁ × ↥((𝓡∂ (m + 1)).boundary M₂))},
      (∀ q ∈ t, ContMDiffAt (I₁.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) J n g q) →
      (∀ q ∈ t, ¬ IsRegularPoint (I₁.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin m))) J g q) →
      IsNullSet J (g '' t)) :
    IsNullSet J (f '' (s ∩ (univ : Set M₁) ×ˢ (𝓡∂ (m + 1)).boundary M₂)) := by
  have : IsManifold (𝓡∂ (m + 1)) 1 M₂ := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) n ↥((𝓡∂ (m + 1)).boundary M₂) :=
    isManifold_boundary M₂ hn
  have : SecondCountableTopology ↥((𝓡∂ (m + 1)).boundary M₂) :=
    Topology.IsEmbedding.subtypeVal.secondCountableTopology
  exact isNullSet_image_inter_univ_prod_of_range_eq hn Subtype.range_coe
    (isSmoothEmbedding_subtypeVal_boundary (n := m) (k := n) M₂ hn).contMDiff hf hs hbdry

omit [FiniteDimensional ℝ E'] in
/-- On a product whose right factor is a second-countable quadrant manifold `M₂`, nullity along
`univ ×ˢ (𝓡c (m + 1)).boundary M₂` reduces to nullity on `M₁ × (𝓡c (m + 1)).AbstractBoundary M₂`. -/
private theorem isNullSet_image_inter_univ_prod_boundary_quadrant {n : ℕ∞ω} (hn : n ≠ 0)
    {E₁ H₁ M₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
    {m : ℕ} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant (m + 1)) M₂]
    [SecondCountableTopology M₂] [IsManifold (𝓡c (m + 1)) n M₂]
    {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hf : ∀ x ∈ s, ContMDiffAt (I₁.prod (𝓡c (m + 1))) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (I₁.prod (𝓡c (m + 1))) J f x)
    (hbdry : ∀ [SecondCountableTopology ((𝓡c (m + 1)).AbstractBoundary M₂)]
      {g : M₁ × (𝓡c (m + 1)).AbstractBoundary M₂ → N}
      {t : Set (M₁ × (𝓡c (m + 1)).AbstractBoundary M₂)},
      (∀ q ∈ t, ContMDiffAt (I₁.prod (𝓡c m)) J n g q) →
      (∀ q ∈ t, ¬ IsRegularPoint (I₁.prod (𝓡c m)) J g q) →
      IsNullSet J (g '' t)) :
    IsNullSet J (f '' (s ∩ (univ : Set M₁) ×ˢ (𝓡c (m + 1)).boundary M₂)) := by
  have : SecondCountableTopology ((𝓡c (m + 1)).AbstractBoundary M₂) :=
    ModelWithCorners.AbstractBoundary.secondCountableTopology
      (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn
  exact isNullSet_image_inter_univ_prod_of_range_eq hn
    (ModelWithCorners.AbstractBoundary.range_point
      (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq (m + 1)) hn)
    ModelWithCorners.AbstractBoundary.contMDiff_point hf hs hbdry

/-- **Sard's theorem on the product of a boundaryless manifold and a quadrant manifold.** -/
theorem isNullSet_image_of_not_isRegularPoint_prod_quadrant
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M]
    [LindelofSpace (P × M)] {n : ℕ∞ω} [IsManifold K n P] [IsManifold (𝓡c d) n M] [IsManifold J n N]
    {f : P × M → N} {s : Set (P × M)}
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (K.prod (𝓡c d)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (K.prod (𝓡c d)) J f x) :
    IsNullSet J (f '' s) := by
  induction d generalizing M with
  | zero =>
    have : (𝓡c 0).Boundaryless := ⟨by simp [range_modelWithCornersEuclideanQuadrant]⟩
    have hk₀ :
        ((finrank ℝ (E₁ × EuclideanSpace ℝ (Fin 0)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa only [Module.finrank_prod, finrank_euclideanSpace_fin, add_zero] using hk
    exact isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk₀ hf hs
  | succ m ih =>
    refine isNullSet_image_prod_of_inter_boundary
      (by simpa only [finrank_euclideanSpace_fin] using hk) hf hs
      (fun hn ↦ isNullSet_image_inter_univ_prod_boundary_quadrant hn hf hs
        (ih (le_trans (Nat.cast_le.2 (by omega)) hk)))
      fun _ ↦ isNullSet_image_inter_boundary_of_boundaryless_left

/-- **Sard's theorem on the product of a quadrant manifold and a boundaryless manifold.** -/
theorem isNullSet_image_of_not_isRegularPoint_quadrant_prod
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M]
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    [LindelofSpace (M × P)] {n : ℕ∞ω} [IsManifold (𝓡c d) n M] [IsManifold K n P] [IsManifold J n N]
    {f : M × P → N} {s : Set (M × P)}
    (hk : ((d + finrank ℝ E₁ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡c d).prod K) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡c d).prod K) J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_swap (fun h ↦ by simp [h] at hk) hf hs
    (isNullSet_image_of_not_isRegularPoint_prod_quadrant (by rwa [add_comm (finrank ℝ E₁) d]))

/-- The critical values of a `C^k` map on the product of a boundaryless manifold and a quadrant
manifold form a null set when `k > dim P + d - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_prod_quadrant
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M]
    [LindelofSpace (P × M)] {n : ℕ∞ω} [IsManifold K n P] [IsManifold (𝓡c d) n M] [IsManifold J n N]
    {f : P × M → N} (hf : ContMDiff (K.prod (𝓡c d)) J n f)
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (K.prod (𝓡c d)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_prod_quadrant hk (fun x _ ↦ hf x) fun _ hx ↦ hx

/-- The critical values of a `C^k` map on the product of a quadrant manifold and a boundaryless
manifold form a null set when `k > d + dim P - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant_prod
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M]
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    [LindelofSpace (M × P)] {n : ℕ∞ω} [IsManifold (𝓡c d) n M] [IsManifold K n P] [IsManifold J n N]
    {f : M × P → N} (hf : ContMDiff ((𝓡c d).prod K) J n f)
    (hk : ((d + finrank ℝ E₁ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡c d).prod K) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_quadrant_prod hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on the product of a boundaryless manifold and a quadrant
manifold are dense when `k > dim P + d - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_prod_quadrant
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M]
    [LindelofSpace (P × M)] {n : ℕ∞ω} [IsManifold K n P] [IsManifold (𝓡c d) n M] [IsManifold J n N]
    {f : P × M → N} (hf : ContMDiff (K.prod (𝓡c d)) J n f)
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (K.prod (𝓡c d)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_prod_quadrant hk).dense_compl

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on the product of a quadrant manifold and a boundaryless
manifold are dense when `k > d + dim P - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant_prod
    {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant d) M]
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    [LindelofSpace (M × P)] {n : ℕ∞ω} [IsManifold (𝓡c d) n M] [IsManifold K n P] [IsManifold J n N]
    {f : M × P → N} (hf : ContMDiff ((𝓡c d).prod K) J n f)
    (hk : ((d + finrank ℝ E₁ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡c d).prod K) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant_prod hk).dense_compl

/-- **Sard's theorem on the product of a boundaryless manifold and a manifold with boundary.** -/
theorem isNullSet_image_of_not_isRegularPoint_prod_halfSpace
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    {d : ℕ} [NeZero d] {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
    [LindelofSpace (P × M)] {n : ℕ∞ω} [IsManifold K n P] [IsManifold (𝓡∂ d) n M] [IsManifold J n N]
    {f : P × M → N} {s : Set (P × M)}
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (K.prod (𝓡∂ d)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint (K.prod (𝓡∂ d)) J f x) :
    IsNullSet J (f '' s) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d)
  refine isNullSet_image_prod_of_inter_boundary
    (by simpa only [finrank_euclideanSpace_fin] using hk) hf hs
    (fun hn ↦ isNullSet_image_inter_univ_prod_boundary_halfSpace hn hf hs
      (isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
        (le_trans (Nat.cast_le.2 (by rw [Module.finrank_prod, finrank_euclideanSpace_fin]; omega))
          hk)))
    fun _ ↦ isNullSet_image_inter_boundary_of_boundaryless_left

/-- **Sard's theorem on the product of a manifold with boundary and a boundaryless manifold.** -/
theorem isNullSet_image_of_not_isRegularPoint_halfSpace_prod
    {d : ℕ} [NeZero d] {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    [LindelofSpace (M × P)] {n : ℕ∞ω} [IsManifold (𝓡∂ d) n M] [IsManifold K n P] [IsManifold J n N]
    {f : M × P → N} {s : Set (M × P)}
    (hk : ((d + finrank ℝ E₁ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡∂ d).prod K) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡∂ d).prod K) J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_swap (fun h ↦ by simp [h] at hk) hf hs
    (isNullSet_image_of_not_isRegularPoint_prod_halfSpace (by rwa [add_comm (finrank ℝ E₁) d]))

/-- The critical values of a `C^k` map on the product of a boundaryless manifold and a manifold
with boundary form a null set when `k > dim P + d - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_prod_halfSpace
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    {d : ℕ} [NeZero d] {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
    [LindelofSpace (P × M)] {n : ℕ∞ω} [IsManifold K n P] [IsManifold (𝓡∂ d) n M] [IsManifold J n N]
    {f : P × M → N} (hf : ContMDiff (K.prod (𝓡∂ d)) J n f)
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (K.prod (𝓡∂ d)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_prod_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

/-- The critical values of a `C^k` map on the product of a manifold with boundary and a
boundaryless manifold form a null set when `k > d + dim P - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod
    {d : ℕ} [NeZero d] {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    [LindelofSpace (M × P)] {n : ℕ∞ω} [IsManifold (𝓡∂ d) n M] [IsManifold K n P] [IsManifold J n N]
    {f : M × P → N} (hf : ContMDiff ((𝓡∂ d).prod K) J n f)
    (hk : ((d + finrank ℝ E₁ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡∂ d).prod K) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_halfSpace_prod hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on the product of a boundaryless manifold and a manifold with
boundary are dense when `k > dim P + d - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_prod_halfSpace
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    {d : ℕ} [NeZero d] {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
    [LindelofSpace (P × M)] {n : ℕ∞ω} [IsManifold K n P] [IsManifold (𝓡∂ d) n M] [IsManifold J n N]
    {f : P × M → N} (hf : ContMDiff (K.prod (𝓡∂ d)) J n f)
    (hk : ((finrank ℝ E₁ + d - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (K.prod (𝓡∂ d)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_prod_halfSpace hk).dense_compl

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on the product of a manifold with boundary and a boundaryless
manifold are dense when `k > d + dim P - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace_prod
    {d : ℕ} [NeZero d] {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace d) M]
    {E₁ H₁ P : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {K : ModelWithCorners ℝ E₁ H₁}
    [TopologicalSpace P] [ChartedSpace H₁ P] [BoundarylessManifold K P]
    [LindelofSpace (M × P)] {n : ℕ∞ω} [IsManifold (𝓡∂ d) n M] [IsManifold K n P] [IsManifold J n N]
    {f : M × P → N} (hf : ContMDiff ((𝓡∂ d).prod K) J n f)
    (hk : ((d + finrank ℝ E₁ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡∂ d).prod K) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace_prod hk).dense_compl

/-- **Sard's theorem on the product of two manifolds with boundary.** -/
theorem isNullSet_image_of_not_isRegularPoint_halfSpace_prod_halfSpace
    {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡∂ d₁) n M₁] [IsManifold (𝓡∂ d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡∂ d₁).prod (𝓡∂ d₂)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡∂ d₁).prod (𝓡∂ d₂)) J f x) :
    IsNullSet J (f '' s) := by
  obtain ⟨m₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d₁)
  obtain ⟨m₂, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d₂)
  refine isNullSet_image_prod_of_inter_boundary
    (by simpa only [finrank_euclideanSpace_fin] using hk) hf hs
    (fun hn ↦ isNullSet_image_inter_univ_prod_boundary_halfSpace hn hf hs
      (isNullSet_image_of_not_isRegularPoint_halfSpace_prod
        (le_trans (Nat.cast_le.2 (by rw [finrank_euclideanSpace_fin]; omega)) hk)))
    fun hn ↦ isNullSet_image_inter_prod_univ_of_swap hn hf hs fun hfg hsfg ↦
      isNullSet_image_inter_univ_prod_boundary_halfSpace hn hfg hsfg
        (isNullSet_image_of_not_isRegularPoint_halfSpace_prod
          (le_trans (Nat.cast_le.2 (by rw [finrank_euclideanSpace_fin]; omega)) hk))

/-- The critical values of a `C^k` map on the product of two manifolds with boundary form a null
set when `k > d₁ + d₂ - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod_halfSpace
    {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡∂ d₁) n M₁] [IsManifold (𝓡∂ d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} (hf : ContMDiff ((𝓡∂ d₁).prod (𝓡∂ d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡∂ d₁).prod (𝓡∂ d₂)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_halfSpace_prod_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on the product of two manifolds with boundary are dense when
`k > d₁ + d₂ - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace_prod_halfSpace
    {d₁ d₂ : ℕ} [NeZero d₁] [NeZero d₂]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡∂ d₁) n M₁] [IsManifold (𝓡∂ d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} (hf : ContMDiff ((𝓡∂ d₁).prod (𝓡∂ d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡∂ d₁).prod (𝓡∂ d₂)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace_prod_halfSpace hk).dense_compl

/-- **Sard's theorem on the product of a manifold with boundary and a quadrant manifold.** -/
theorem isNullSet_image_of_not_isRegularPoint_halfSpace_prod_quadrant
    {d₁ d₂ : ℕ} [NeZero d₁]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡∂ d₁) n M₁] [IsManifold (𝓡c d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡∂ d₁).prod (𝓡c d₂)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡∂ d₁).prod (𝓡c d₂)) J f x) :
    IsNullSet J (f '' s) := by
  induction d₂ generalizing M₂ with
  | zero =>
    have : (𝓡c 0).Boundaryless := ⟨by simp [range_modelWithCornersEuclideanQuadrant]⟩
    have hk₀ :
        ((d₁ + finrank ℝ (EuclideanSpace ℝ (Fin 0)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
      simpa only [finrank_euclideanSpace_fin] using hk
    exact isNullSet_image_of_not_isRegularPoint_halfSpace_prod hk₀ hf hs
  | succ m₂ ih =>
    obtain ⟨m₁, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne d₁)
    refine isNullSet_image_prod_of_inter_boundary
      (by simpa only [finrank_euclideanSpace_fin] using hk) hf hs
      (fun hn ↦ isNullSet_image_inter_univ_prod_boundary_quadrant hn hf hs
        (ih (le_trans (Nat.cast_le.2 (by omega)) hk)))
      fun hn ↦ isNullSet_image_inter_prod_univ_of_swap hn hf hs fun hfg hsfg ↦
        isNullSet_image_inter_univ_prod_boundary_halfSpace hn hfg hsfg
          (isNullSet_image_of_not_isRegularPoint_quadrant_prod
            (le_trans (Nat.cast_le.2 (by rw [finrank_euclideanSpace_fin]; omega)) hk))

/-- **Sard's theorem on the product of a quadrant manifold and a manifold with boundary.** -/
theorem isNullSet_image_of_not_isRegularPoint_quadrant_prod_halfSpace
    {d₁ d₂ : ℕ} [NeZero d₂]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡c d₁) n M₁] [IsManifold (𝓡∂ d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡c d₁).prod (𝓡∂ d₂)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡c d₁).prod (𝓡∂ d₂)) J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_swap (fun h ↦ by simp [h] at hk) hf hs
    (isNullSet_image_of_not_isRegularPoint_halfSpace_prod_quadrant (by rwa [add_comm d₂ d₁]))

/-- The critical values of a `C^k` map on the product of a manifold with boundary and a quadrant
manifold form a null set when `k > d₁ + d₂ - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace_prod_quadrant
    {d₁ d₂ : ℕ} [NeZero d₁]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡∂ d₁) n M₁] [IsManifold (𝓡c d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} (hf : ContMDiff ((𝓡∂ d₁).prod (𝓡c d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡∂ d₁).prod (𝓡c d₂)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_halfSpace_prod_quadrant hk (fun x _ ↦ hf x) fun _ hx ↦ hx

/-- The critical values of a `C^k` map on the product of a quadrant manifold and a manifold with
boundary form a null set when `k > d₁ + d₂ - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant_prod_halfSpace
    {d₁ d₂ : ℕ} [NeZero d₂]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡c d₁) n M₁] [IsManifold (𝓡∂ d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} (hf : ContMDiff ((𝓡c d₁).prod (𝓡∂ d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡c d₁).prod (𝓡∂ d₂)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_quadrant_prod_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on the product of a manifold with boundary and a quadrant
manifold are dense when `k > d₁ + d₂ - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace_prod_quadrant
    {d₁ d₂ : ℕ} [NeZero d₁]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanHalfSpace d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡∂ d₁) n M₁] [IsManifold (𝓡c d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} (hf : ContMDiff ((𝓡∂ d₁).prod (𝓡c d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡∂ d₁).prod (𝓡c d₂)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace_prod_quadrant hk).dense_compl

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on the product of a quadrant manifold and a manifold with
boundary are dense when `k > d₁ + d₂ - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant_prod_halfSpace
    {d₁ d₂ : ℕ} [NeZero d₂]
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanHalfSpace d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡c d₁) n M₁] [IsManifold (𝓡∂ d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} (hf : ContMDiff ((𝓡c d₁).prod (𝓡∂ d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡c d₁).prod (𝓡∂ d₂)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant_prod_halfSpace hk).dense_compl

/-- **Sard's theorem on the product of two quadrant manifolds.** -/
theorem isNullSet_image_of_not_isRegularPoint_quadrant_prod_quadrant
    {d₁ d₂ : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡c d₁) n M₁] [IsManifold (𝓡c d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} {s : Set (M₁ × M₂)}
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡c d₁).prod (𝓡c d₂)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡c d₁).prod (𝓡c d₂)) J f x) :
    IsNullSet J (f '' s) := by
  induction hd : d₁ + d₂ using Nat.strongRecOn generalizing d₁ d₂ M₁ M₂ with
  | ind k ih =>
    rcases d₁ with _ | m₁
    · have : (𝓡c 0).Boundaryless := ⟨by simp [range_modelWithCornersEuclideanQuadrant]⟩
      have hk₀ :
          ((finrank ℝ (EuclideanSpace ℝ (Fin 0)) + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
        simpa only [finrank_euclideanSpace_fin] using hk
      exact isNullSet_image_of_not_isRegularPoint_prod_quadrant hk₀ hf hs
    rcases d₂ with _ | m₂
    · have : (𝓡c 0).Boundaryless := ⟨by simp [range_modelWithCornersEuclideanQuadrant]⟩
      have hk₀ :
          ((m₁ + 1 + finrank ℝ (EuclideanSpace ℝ (Fin 0)) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
        simpa only [finrank_euclideanSpace_fin] using hk
      exact isNullSet_image_of_not_isRegularPoint_quadrant_prod hk₀ hf hs
    subst hd
    refine isNullSet_image_prod_of_inter_boundary
      (by simpa only [finrank_euclideanSpace_fin] using hk) hf hs
      (fun hn ↦ isNullSet_image_inter_univ_prod_boundary_quadrant hn hf hs fun hfg hsfg ↦
        ih (m₁ + 1 + m₂) (by omega) (le_trans (Nat.cast_le.2 (by omega)) hk) hfg hsfg rfl)
      fun hn ↦ isNullSet_image_inter_prod_univ_of_swap hn hf hs fun hfg hsfg ↦
        isNullSet_image_inter_univ_prod_boundary_quadrant hn hfg hsfg fun hfg' hsfg' ↦
          isNullSet_image_of_swap hn hfg' hsfg' fun hfg'' hsfg'' ↦
            ih (m₁ + (m₂ + 1)) (by omega) (le_trans (Nat.cast_le.2 (by omega)) hk) hfg'' hsfg'' rfl

/-- The critical values of a `C^k` map on the product of two quadrant manifolds form a null set
when `k > d₁ + d₂ - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant_prod_quadrant
    {d₁ d₂ : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡c d₁) n M₁] [IsManifold (𝓡c d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} (hf : ContMDiff ((𝓡c d₁).prod (𝓡c d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡c d₁).prod (𝓡c d₂)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_quadrant_prod_quadrant hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map on the product of two quadrant manifolds are dense when
`k > d₁ + d₂ - dim N` and `k ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant_prod_quadrant
    {d₁ d₂ : ℕ}
    {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace (EuclideanQuadrant d₁) M₁]
    {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace (EuclideanQuadrant d₂) M₂]
    [LindelofSpace (M₁ × M₂)] {n : ℕ∞ω} [IsManifold (𝓡c d₁) n M₁] [IsManifold (𝓡c d₂) n M₂]
    [IsManifold J n N] {f : M₁ × M₂ → N} (hf : ContMDiff ((𝓡c d₁).prod (𝓡c d₂)) J n f)
    (hk : ((d₁ + d₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡c d₁).prod (𝓡c d₂)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant_prod_quadrant hk).dense_compl

end Product

end TauCeti
