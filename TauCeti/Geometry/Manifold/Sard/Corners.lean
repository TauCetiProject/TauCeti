/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Real
public import TauCeti.Geometry.Manifold.Sard.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import TauCeti.Analysis.Calculus.Sard.Orthant
import TauCeti.Geometry.Manifold.Corners.Depth

/-!
# Sard's theorem for manifolds with boundary and corners

Let `f : M → N` be a `C^k` map from a Lindelöf real manifold `M` with boundary or corners to a
real manifold `N` (which may itself have boundary or corners), modelled on finite-dimensional
spaces of dimensions `m` and `d`. This file proves that at Sard's sharp regularity
`k ≥ max 1 (m - d + 1)` — and in particular for smooth maps — the critical values of `f`, that is
the images of the points where `mfderiv I J f` is not surjective, form a null set of `N`
(`TauCeti.IsNullSet`), and consequently the regular values of `f` are dense in `N`.

Two complementary mechanisms are given:

1. **Cover by boundaryless manifolds.** If a set `s` of critical points of `f` on an arbitrary
   charted space `M` is covered by the ranges of countably many `C^k` maps `g i : P i → M` from
   boundaryless Lindelöf manifolds `P i`, then by the chain rule (`TauCeti.IsRegularPoint.of_comp`)
   every preimage of `s` consists of critical points of `f ∘ g i`, so boundaryless Sard
   (`TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt`) applies on each `P i` at its
   own dimension `finrank ℝ (EP i)`. In particular, once a manifold with corners is decomposed into
   countably many boundaryless strata, nullity of its critical values follows immediately.
2. **Coordinate-orthant models in charts.** When `range I` is cut out in the model vector space `E`
   by the nonnegativity of a subset of coordinates along a basis `b : Module.Basis ι ℝ E`,
   reading `f` in pairs of extended charts reduces directly to the flat orthant Morse--Sard theorem
   `TauCeti.addHaar_image_criticalPoints_within_nonneg_eq_zero`, without installing a separate
   manifold structure on each boundary stratum. Such models include `𝓘(ℝ, E)` (`S = ∅`), the
   Euclidean half-space `𝓡∂ m` (`S = {0}`), the quadrant `𝓡c m` (`S = univ`), and arbitrary finite
   products of these (such as cylinders `M × [0, 1]` modelled on `(𝓡∂ m).prod (𝓡∂ 1)`).

Because chartwise null sets are closed under countable unions and have dense complements, whenever
both `f : M → N` and a countable family of restrictions `f ∘ g i : P i → N` (such as `f` together
with its restriction to `∂M` or to the boundary faces of a cylinder) satisfy Sard's regularity
condition, their simultaneous regular values are dense in `N`.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_subset_range` and
  `TauCeti.isNullSet_image_of_not_isRegularPoint_of_subset_iUnion_range`: Sard's theorem for a set
  of critical points covered by one or countably many maps from boundaryless Lindelöf manifolds.
* `TauCeti.dense_forall_isRegularValue_of_isNullSet`: simultaneous regular values of a countable
  family of maps with null critical values are dense.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_range_eq_setOf_forall_nonneg_repr`,
  `ContMDiff.isNullSet_image_criticalPoints_of_range_eq_setOf_forall_nonneg_repr`,
  `ContMDiff.dense_isRegularValue_of_range_eq_setOf_forall_nonneg_repr`, and
  `TauCeti.isNullSet_image_of_not_isRegularPoint_prod_of_range_eq_setOf_forall_nonneg_repr`: Sard's
  theorem for any model cut out by basis coordinate nonnegativity and for products of two such
  models.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_range_eq`,
  `ContMDiff.isNullSet_image_criticalPoints_of_range_eq`, and
  `ContMDiff.dense_isRegularValue_of_range_eq`: specialization to Euclidean coordinate models
  `range I = {z | ∀ i ∈ S, 0 ≤ z i}`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_halfSpace`,
  `ContMDiff.dense_isRegularValue_halfSpace`, and
  `ContMDiff.dense_isRegularValue_and_comp_halfSpace`: Sard's theorem and simultaneous boundary
  regularity for manifolds with boundary modelled on `𝓡∂ m`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_prod_halfSpace`,
  `ContMDiff.isNullSet_image_criticalPoints_prod_halfSpace`, and
  `ContMDiff.dense_isRegularValue_prod_halfSpace`: Sard's theorem for manifolds with corners
  modelled on `(𝓡∂ m₁).prod (𝓡∂ m₂)`, such as products of manifolds with boundary and cylinders
  `M × [0, 1]`.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_quadrant`,
  `ContMDiff.isNullSet_image_criticalPoints_quadrant`, and
  `ContMDiff.dense_isRegularValue_quadrant`: Sard's theorem for manifolds with corners modelled on
  the quadrant `𝓡c m`.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10.
-/

public section

open Function Module Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace TauCeti

section Cover

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem along a map from a boundaryless manifold.** Let `M` be a charted space, `N` a
`C^n` manifold with corners, and `g : P → M` a map from a boundaryless Lindelöf `C^n` manifold `P`
whose range contains `s`. If `g` is `C^n` on `g ⁻¹' s`, `f` is `C^n` and non-regular on `s`, and
`n` meets Sard's regularity bound for `P` and `N`, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_subset_range
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [LindelofSpace P]
    [BoundarylessManifold IP P] [IsManifold IP n P] {g : P → M}
    (hk : ((finrank ℝ EP - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hsub : s ⊆ range g) (hg : ∀ p, g p ∈ s → ContMDiffAt IP I n g p)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have himg : f '' s = (f ∘ g) '' (g ⁻¹' s) := by
    ext y
    constructor
    · rintro ⟨x, hxs, rfl⟩
      obtain ⟨p, rfl⟩ := hsub hxs
      exact ⟨p, hxs, rfl⟩
    · rintro ⟨p, hps, rfl⟩
      exact ⟨g p, hps, rfl⟩
  rw [himg]
  refine isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk
    (fun p hp ↦ (hf (g p) hp).comp p (hg p hp)) fun p hp hreg ↦ hs (g p) hp ?_
  exact hreg.of_comp ((hf (g p) hp).mdifferentiableAt hn) ((hg p hp).mdifferentiableAt hn)

/-- **Sard's theorem for a countable cover by boundaryless manifolds.** If a set `s` of critical
points of `f : M → N` is covered by the ranges of countably many maps `g i : P i → M` from
boundaryless Lindelöf `C^n` manifolds `P i`, each satisfying Sard's regularity bound for its own
dimension, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_subset_iUnion_range
    {ι : Sort*} [Countable ι]
    {EP : ι → Type*} [∀ i, NormedAddCommGroup (EP i)] [∀ i, NormedSpace ℝ (EP i)]
    [∀ i, FiniteDimensional ℝ (EP i)]
    {HP : ι → Type*} [∀ i, TopologicalSpace (HP i)]
    {IP : ∀ i, ModelWithCorners ℝ (EP i) (HP i)}
    {P : ι → Type*} [∀ i, TopologicalSpace (P i)] [∀ i, ChartedSpace (HP i) (P i)]
    [∀ i, LindelofSpace (P i)] [∀ i, BoundarylessManifold (IP i) (P i)]
    [∀ i, IsManifold (IP i) n (P i)] {g : ∀ i, P i → M}
    (hk : ∀ i, ((finrank ℝ (EP i) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hsub : s ⊆ ⋃ i, range (g i)) (hg : ∀ i p, g i p ∈ s → ContMDiffAt (IP i) I n (g i) p)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  have hsEq : s = ⋃ i, s ∩ range (g i) := by
    rw [← inter_iUnion, inter_eq_left.2 hsub]
  rw [hsEq, image_iUnion]
  refine IsNullSet.iUnion fun i ↦ ?_
  exact isNullSet_image_of_not_isRegularPoint_of_subset_range (hk i) inter_subset_right
    (fun p hp ↦ hg i p hp.1) (fun x hx ↦ hf x hx.1) (fun x hx ↦ hs x hx.1)

end Cover

section SimultaneousRegularValue

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]

/-- If a countable family of maps into a finite-dimensional real manifold `N` each have a null set
of critical values, then the values in `N` that are simultaneously regular for every map in the
family are dense in `N`. Nullity is essential here: density of each individual regular-value set
would not be closed under intersections. -/
theorem dense_forall_isRegularValue_of_isNullSet {ι : Sort*} [Countable ι]
    {EP : ι → Type*} [∀ i, NormedAddCommGroup (EP i)] [∀ i, NormedSpace ℝ (EP i)]
    {HP : ι → Type*} [∀ i, TopologicalSpace (HP i)]
    {IP : ∀ i, ModelWithCorners ℝ (EP i) (HP i)}
    {P : ι → Type*} [∀ i, TopologicalSpace (P i)] [∀ i, ChartedSpace (HP i) (P i)]
    {g : ∀ i, P i → N}
    (hnull : ∀ i, IsNullSet J (g i '' {p | ¬ IsRegularPoint (IP i) J (g i) p})) :
    Dense {y : N | ∀ i, IsRegularValue (IP i) J (g i) y} := by
  have hEq : {y : N | ∀ i, IsRegularValue (IP i) J (g i) y} =
      (⋃ i, g i '' {p | ¬ IsRegularPoint (IP i) J (g i) p})ᶜ := by
    ext y
    simp [isRegularValue_iff_notMem_image]
  rw [hEq]
  exact (IsNullSet.iUnion hnull).dense_compl

end SimultaneousRegularValue

section BasisModel

/-- Models with corners whose ranges are cut out by the nonnegativity of subsets of basis
coordinates are closed under products, using the product basis `b₁.prod b₂`. -/
private theorem range_prod_eq_setOf_forall_nonneg_repr
    {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
    {I₁ : ModelWithCorners ℝ E₁ H₁} {ι₁ : Type*} {b₁ : Module.Basis ι₁ ℝ E₁} {S₁ : Set ι₁}
    (hI₁ : range I₁ = {x : E₁ | ∀ i ∈ S₁, 0 ≤ b₁.repr x i})
    {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
    {I₂ : ModelWithCorners ℝ E₂ H₂} {ι₂ : Type*} {b₂ : Module.Basis ι₂ ℝ E₂} {S₂ : Set ι₂}
    (hI₂ : range I₂ = {x : E₂ | ∀ j ∈ S₂, 0 ≤ b₂.repr x j}) :
    range (I₁.prod I₂) =
      {z : E₁ × E₂ | ∀ k ∈ Sum.inl '' S₁ ∪ Sum.inr '' S₂, 0 ≤ (b₁.prod b₂).repr z k} := by
  ext ⟨x₁, x₂⟩
  rw [ModelWithCorners.range_prod, hI₁, hI₂]
  simp only [mem_prod, mem_ofPred_eq, mem_union, mem_image]
  constructor
  · rintro ⟨hx₁, hx₂⟩ k (⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩)
    · simpa using hx₁ i hi
    · simpa using hx₂ j hj
  · intro h
    exact ⟨fun i hi ↦ by simpa using h (Sum.inl i) (Or.inl ⟨i, hi, rfl⟩),
      fun j hj ↦ by simpa using h (Sum.inr j) (Or.inr ⟨j, hj, rfl⟩)⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*} {b : Module.Basis ι ℝ E} {S : Set ι}
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for basis-orthant models.** Let `M` be a Lindelöf `C^n` manifold modelled on
`I : ModelWithCorners ℝ E H`, where `range I` is cut out by the nonnegativity of the
`S`-coordinates of a basis `b : Module.Basis ι ℝ E`, and let `N` be a `C^n` manifold with corners.
If `f : M → N` is `C^n` and non-regular at every point of `s`, with
`n > finrank ℝ E - finrank ℝ E'` and `n ≥ 1`, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_range_eq_setOf_forall_nonneg_repr
    (hI : range I = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i})
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have : IsManifold I 1 M := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold J 1 N := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  refine isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ μ _ ↦ ?_
  set g : E → E' := extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm
  set U : Set E := extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source)
  have hU : U ⊆ {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} := by
    rintro _ ⟨x, -, rfl⟩
    rw [← hI, extChartAt_coe]
    exact mem_range_self _
  have key : ∀ z ∈ U, ContDiffWithinAt ℝ n g {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} z ∧
      ¬ Surjective (fderivWithin ℝ g {x : E | ∀ i ∈ S, 0 ≤ b.repr x i} z) := by
    rintro _ ⟨x, hx, rfl⟩
    have hsmooth : ContDiffWithinAt ℝ n g (range I) (extChartAt I x₀ x) :=
      ((contMDiffAt_iff_of_mem_source hx.1.2 hx.2).1 (hf x hx.1.1)).2
    have hcrit : ¬ Surjective (fderivWithin ℝ g (range I) (extChartAt I x₀ x)) :=
      (isRegularPoint_iff_surjective_fderivWithin ((hf x hx.1.1).mdifferentiableAt hn)
        hx.1.2 hx.2).not.mp (hs x hx.1.1)
    rw [hI] at hsmooth hcrit
    exact ⟨hsmooth, hcrit⟩
  refine measure_mono_null (image_mono ?_)
    (addHaar_image_criticalPoints_within_nonneg_eq_zero μ hU (fun z hz ↦ (key z hz).1) hk)
  exact fun z hz ↦ ⟨hz, (key z hz).2⟩

/-- **Sard's theorem for basis-orthant models.** For a `C^n` map `f : M → N` from a Lindelöf
manifold modelled on `I` with `range I = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}`, the critical values
form a null set in `N` when `n > finrank ℝ E - finrank ℝ E'` and `n ≥ 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_range_eq_setOf_forall_nonneg_repr
    (hf : ContMDiff I J n f) (hI : range I = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i})
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_range_eq_setOf_forall_nonneg_repr hI hk
    (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- For a `C^n` map `f : M → N` from a Lindelöf manifold modelled on `I` with
`range I = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}`, the regular values of `f` are dense in `N` when
`n > finrank ℝ E - finrank ℝ E'` and `n ≥ 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_range_eq_setOf_forall_nonneg_repr
    (hf : ContMDiff I J n f) (hI : range I = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i})
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_of_range_eq_setOf_forall_nonneg_repr hI hk).dense_compl

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- Simultaneous density of regular values on a manifold with boundary or corners and along a
countable family of maps from boundaryless Lindelöf manifolds (such as boundary or corner faces).
If `f : M → N` is `C^n` on `M` with `range I = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i}` and each
`g a : P a → M` is `C^n`, then at Sard's regularity the values in `N` that are regular for `f` and
for every `f ∘ g a` are dense in `N`. -/
theorem _root_.ContMDiff.dense_isRegularValue_and_forall_comp_of_range_eq_setOf_forall_nonneg_repr
    {α : Sort*} [Countable α]
    {EP : α → Type*} [∀ a, NormedAddCommGroup (EP a)] [∀ a, NormedSpace ℝ (EP a)]
    [∀ a, FiniteDimensional ℝ (EP a)]
    {HP : α → Type*} [∀ a, TopologicalSpace (HP a)]
    {IP : ∀ a, ModelWithCorners ℝ (EP a) (HP a)}
    {P : α → Type*} [∀ a, TopologicalSpace (P a)] [∀ a, ChartedSpace (HP a) (P a)]
    [∀ a, LindelofSpace (P a)] [∀ a, BoundarylessManifold (IP a) (P a)]
    [∀ a, IsManifold (IP a) n (P a)] {g : ∀ a, P a → M}
    (hf : ContMDiff I J n f) (hg : ∀ a, ContMDiff (IP a) I n (g a))
    (hI : range I = {x : E | ∀ i ∈ S, 0 ≤ b.repr x i})
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hkP : ∀ a, ((finrank ℝ (EP a) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y : N | IsRegularValue I J f y ∧ ∀ a, IsRegularValue (IP a) J (f ∘ g a) y} := by
  borelize E'
  have hnull : IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x} ∪
      ⋃ a, (f ∘ g a) '' {p | ¬ IsRegularPoint (IP a) J (f ∘ g a) p}) :=
    (hf.isNullSet_image_criticalPoints_of_range_eq_setOf_forall_nonneg_repr hI hk).union
      (IsNullSet.iUnion fun a ↦ (hf.comp (hg a)).isNullSet_image_criticalPoints (hkP a))
  have hEq : {y : N | IsRegularValue I J f y ∧ ∀ a, IsRegularValue (IP a) J (f ∘ g a) y} =
      (f '' {x | ¬ IsRegularPoint I J f x} ∪
        ⋃ a, (f ∘ g a) '' {p | ¬ IsRegularPoint (IP a) J (f ∘ g a) p})ᶜ := by
    ext y
    simp [isRegularValue_iff_notMem_image]
  rw [hEq]
  exact hnull.dense_compl

end BasisModel

section ProdBasisModel

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold J n N]

/-- **Sard's theorem for products of basis-orthant models.** If `I₁` and `I₂` have ranges cut out
by basis coordinate nonnegativity, then so does `I₁.prod I₂`, so a `C^n` map out of a Lindelöf
`C^n` manifold modelled on `I₁.prod I₂` sends every set `s` of non-regular points to a null set
when `n ≥ finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1`. -/
theorem isNullSet_image_of_not_isRegularPoint_prod_of_range_eq_setOf_forall_nonneg_repr
    {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁}
    {ι₁ : Type*} {b₁ : Module.Basis ι₁ ℝ E₁} {S₁ : Set ι₁}
    {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [TopologicalSpace H₂] {I₂ : ModelWithCorners ℝ E₂ H₂}
    {ι₂ : Type*} {b₂ : Module.Basis ι₂ ℝ E₂} {S₂ : Set ι₂}
    {P : Type*} [TopologicalSpace P] [ChartedSpace (ModelProd H₁ H₂) P] [LindelofSpace P]
    [IsManifold (I₁.prod I₂) n P] {g : P → N} {t : Set P}
    (hI₁ : range I₁ = {x : E₁ | ∀ i ∈ S₁, 0 ≤ b₁.repr x i})
    (hI₂ : range I₂ = {x : E₂ | ∀ j ∈ S₂, 0 ≤ b₂.repr x j})
    (hk : ((finrank ℝ E₁ + finrank ℝ E₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hg : ∀ p ∈ t, ContMDiffAt (I₁.prod I₂) J n g p)
    (ht : ∀ p ∈ t, ¬ IsRegularPoint (I₁.prod I₂) J g p) :
    IsNullSet J (g '' t) := by
  refine isNullSet_image_of_not_isRegularPoint_of_range_eq_setOf_forall_nonneg_repr
    (range_prod_eq_setOf_forall_nonneg_repr hI₁ hI₂) ?_ hg ht
  rwa [Module.finrank_prod]

end ProdBasisModel

section EuclideanCoordinates

variable {κ : Type*} [Fintype κ] {S : Set κ}
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ (EuclideanSpace ℝ κ) H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for Euclidean coordinate-nonnegativity models**, on a set. For a Lindelöf
`C^n` manifold `M` whose model `I` on `EuclideanSpace ℝ κ` has `range I = {z | ∀ i ∈ S, 0 ≤ z i}`,
if `f : M → N` is `C^n` and non-regular on `s` with `n ≥ Fintype.card κ - finrank ℝ E' + 1`, then
`f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_range_eq
    (hI : range I = {z : EuclideanSpace ℝ κ | ∀ i ∈ S, 0 ≤ z i})
    (hk : ((Fintype.card κ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  have hk' : ((finrank ℝ (EuclideanSpace ℝ κ) - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n := by
    rwa [finrank_euclideanSpace]
  exact isNullSet_image_of_not_isRegularPoint_of_range_eq_setOf_forall_nonneg_repr
    (b := PiLp.basisFun 2 ℝ κ) (by simpa [PiLp.basisFun_repr] using hI) hk' hf hs

/-- **Sard's theorem for Euclidean coordinate-nonnegativity models.** For a `C^n` map `f : M → N`
from a Lindelöf manifold with `range I = {z : EuclideanSpace ℝ κ | ∀ i ∈ S, 0 ≤ z i}`, the critical
values form a null set in `N` when `n ≥ Fintype.card κ - finrank ℝ E' + 1`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_range_eq
    (hf : ContMDiff I J n f) (hI : range I = {z : EuclideanSpace ℝ κ | ∀ i ∈ S, 0 ≤ z i})
    (hk : ((Fintype.card κ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_range_eq hI hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- For a `C^n` map `f : M → N` from a Lindelöf manifold with
`range I = {z : EuclideanSpace ℝ κ | ∀ i ∈ S, 0 ≤ z i}`, the regular values of `f` are dense in
`N` when `n ≥ Fintype.card κ - finrank ℝ E' + 1`. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_range_eq
    (hf : ContMDiff I J n f) (hI : range I = {z : EuclideanSpace ℝ κ | ∀ i ∈ S, 0 ≤ z i})
    (hk : ((Fintype.card κ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_of_range_eq hI hk).dense_compl

end EuclideanCoordinates

section HalfSpace

variable {m : ℕ} [NeZero m]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace m) M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold (𝓡∂ m) n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with boundary**, on a set. Let `M` be a Lindelöf `C^n` manifold
with boundary modelled on `𝓡∂ m` and `N` a `C^n` manifold modelled on `E'`. If `f : M → N` is `C^n`
and non-regular at every point of `s`, with `n ≥ m - finrank ℝ E' + 1` (in particular if `n = ∞`),
then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_halfSpace
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡∂ m) J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡∂ m) J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_range_eq
    (ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq m)
    (by simpa [Fintype.card_fin] using hk) hf hs

/-- **Sard's theorem for manifolds with boundary.** The critical values of a `C^n` map from a
Lindelöf manifold with boundary modelled on `𝓡∂ m` to a manifold modelled on `E'` form a null set
when `n ≥ m - finrank ℝ E' + 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_halfSpace (hf : ContMDiff (𝓡∂ m) J n f)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡∂ m) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^n` map from a Lindelöf manifold with boundary modelled on `𝓡∂ m` to
a manifold modelled on `E'` are dense when `n ≥ m - finrank ℝ E' + 1`, in particular when the map
is smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_halfSpace (hf : ContMDiff (𝓡∂ m) J n f)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (𝓡∂ m) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_halfSpace hk).dense_compl

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- Simultaneous density of regular values for a `C^n` map `f : M → N` on a Lindelöf manifold with
boundary modelled on `𝓡∂ m` and for its composite `f ∘ g : P → N` along a `C^n` map `g : P → M`
from a boundaryless Lindelöf manifold `P` (such as `∂M`). -/
theorem _root_.ContMDiff.dense_isRegularValue_and_comp_halfSpace
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP]
    {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP}
    {P : Type*} [TopologicalSpace P] [ChartedSpace HP P] [LindelofSpace P]
    [BoundarylessManifold IP P] [IsManifold IP n P] {g : P → M}
    (hf : ContMDiff (𝓡∂ m) J n f) (hg : ContMDiff IP (𝓡∂ m) n g)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hkP : ((finrank ℝ EP - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y : N | IsRegularValue (𝓡∂ m) J f y ∧ IsRegularValue IP J (f ∘ g) y} := by
  have hd := hf.dense_isRegularValue_and_forall_comp_of_range_eq_setOf_forall_nonneg_repr
    (b := PiLp.basisFun 2 ℝ (Fin m)) (S := ({0} : Set (Fin m)))
    (α := Unit) (IP := fun _ ↦ IP) (P := fun _ ↦ P) (g := fun _ ↦ g) (fun _ ↦ hg)
    (by
      ext z
      simp [ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq, PiLp.basisFun_repr])
    (by simpa [finrank_euclideanSpace_fin] using hk) (fun _ ↦ hkP)
  simpa using hd

end HalfSpace

section ProdHalfSpace

variable {m₁ m₂ : ℕ} [NeZero m₁] [NeZero m₂]
  {M : Type*} [TopologicalSpace M]
  [ChartedSpace (ModelProd (EuclideanHalfSpace m₁) (EuclideanHalfSpace m₂)) M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold ((𝓡∂ m₁).prod (𝓡∂ m₂)) n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for products of half-space models**, on a set. This covers products of
manifolds with boundary — in particular cylinders `M₀ × [0, 1]` modelled on `(𝓡∂ m₁).prod (𝓡∂ 1)`
— at Sard's sharp regularity `n ≥ m₁ + m₂ - finrank ℝ E' + 1`. -/
theorem isNullSet_image_of_not_isRegularPoint_prod_halfSpace
    (hk : ((m₁ + m₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt ((𝓡∂ m₁).prod (𝓡∂ m₂)) J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint ((𝓡∂ m₁).prod (𝓡∂ m₂)) J f x) :
    IsNullSet J (f '' s) := by
  refine isNullSet_image_of_not_isRegularPoint_prod_of_range_eq_setOf_forall_nonneg_repr
    (b₁ := PiLp.basisFun 2 ℝ (Fin m₁)) (S₁ := ({0} : Set (Fin m₁)))
    (b₂ := PiLp.basisFun 2 ℝ (Fin m₂)) (S₂ := ({0} : Set (Fin m₂)))
    (by
      ext z
      simp [ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq, PiLp.basisFun_repr])
    (by
      ext z
      simp [ModelWithCorners.range_modelWithCornersEuclideanHalfSpace_eq, PiLp.basisFun_repr])
    ?_ hf hs
  simpa [finrank_euclideanSpace_fin] using hk

/-- **Sard's theorem for products of half-space models.** For a `C^n` map `f : M → N` out of a
Lindelöf manifold modelled on `(𝓡∂ m₁).prod (𝓡∂ m₂)` (such as `M₁ × M₂` or a cylinder
`M₁ × [0, 1]`), the critical values form a null set in `N` when
`n ≥ m₁ + m₂ - finrank ℝ E' + 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_prod_halfSpace
    (hf : ContMDiff ((𝓡∂ m₁).prod (𝓡∂ m₂)) J n f)
    (hk : ((m₁ + m₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint ((𝓡∂ m₁).prod (𝓡∂ m₂)) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_prod_halfSpace hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- For a `C^n` map `f : M → N` out of a Lindelöf manifold modelled on `(𝓡∂ m₁).prod (𝓡∂ m₂)`
(such as `M₁ × M₂` or a cylinder `M₁ × [0, 1]`), the regular values of `f` are dense in `N` when
`n ≥ m₁ + m₂ - finrank ℝ E' + 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_prod_halfSpace
    (hf : ContMDiff ((𝓡∂ m₁).prod (𝓡∂ m₂)) J n f)
    (hk : ((m₁ + m₂ - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue ((𝓡∂ m₁).prod (𝓡∂ m₂)) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_prod_halfSpace hk).dense_compl

end ProdHalfSpace

section Quadrant

variable {m : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanQuadrant m) M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold (𝓡c m) n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

/-- **Sard's theorem for manifolds with corners modelled on the quadrant `𝓡c m`**, on a set. If `M`
is Lindelöf and `f : M → N` is `C^n` and non-regular at every point of `s`, with
`n ≥ m - finrank ℝ E' + 1` (in particular if `n = ∞`), then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_quadrant
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt (𝓡c m) J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint (𝓡c m) J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_range_eq
    (ModelWithCorners.range_modelWithCornersEuclideanQuadrant_eq m)
    (by simpa [Fintype.card_fin] using hk) hf hs

/-- **Sard's theorem for manifolds with corners modelled on the quadrant `𝓡c m`.** The critical
values of a `C^n` map from a Lindelöf manifold modelled on `𝓡c m` to a manifold modelled on `E'`
form a null set when `n ≥ m - finrank ℝ E' + 1`, in particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_quadrant (hf : ContMDiff (𝓡c m) J n f)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint (𝓡c m) J f x}) :=
  isNullSet_image_of_not_isRegularPoint_quadrant hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^n` map from a Lindelöf manifold with corners modelled on `𝓡c m` to a
manifold modelled on `E'` are dense when `n ≥ m - finrank ℝ E' + 1`, in particular when the map is
smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue_quadrant (hf : ContMDiff (𝓡c m) J n f)
    (hk : ((m - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue (𝓡c m) J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_quadrant hk).dense_compl

end Quadrant

end TauCeti
