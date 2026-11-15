/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Analysis.Calculus.Sard.LowDimension
import TauCeti.Analysis.Calculus.Sard.OutermostStratum

/-!
# Sard's theorem for maps between manifolds of arbitrary dimensions

Let `f : M → N` be a map between real manifolds modelled on finite-dimensional spaces `E` and
`E'`, of dimensions `m` and `n`, with `M` Lindelöf (for instance second countable). This file
proves that the critical values of `f`, the images of the points where `mfderiv I J f` is not
surjective, form a null set of `N`: their image in every chart of `N` is null for every Haar
measure on `E'` (`TauCeti.IsNullSet`). No measure on `N` itself is chosen. The regularity needed
depends on the dimensions.

* If `m < n`, every point is critical and the whole image of a differentiable map is null; here
  `M` and `N` may have boundary or corners.
* In general, a `C^k` map with `k > m - n` and `k ≥ 1` suffices, in particular a smooth map. This
  is the sharp regularity of Sard's theorem: Whitney's example shows that a `C¹` function on the
  plane can have critical values of positive measure.

Each statement only asks for the regularity at the points of a given set `s` of critical points,
so it applies to maps that are only defined, or only regular, on an open subset of `M`. At interior
points of `M` (`I.IsInteriorPoint x`), the extended chart target is a neighbourhood of the chart
image in the model vector space, so the flat theorem applies without any boundaryless assumption on
the model (`TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_isInteriorPoint`). This
yields Sard's theorem for every boundaryless manifold (`[BoundarylessManifold I M]`, including
open subsets of the interior of a manifold with boundary or corners), and reduces Sard's theorem on
a manifold with boundary or corners to a countable family of `C^k` maps covering its boundary
(`TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_iUnion_range`).

The proofs read `f` in pairs of extended charts and apply the corresponding theorem for maps
between normed spaces (`TauCeti.addHaar_image_criticalPoints_eq_zero` and
`DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank`). A countable family of charts
covers `M` (`TauCeti.isNullSet_image_of_forall_addHaar_image_extChartAt`), and since nullity is
tested in every chart of `N`, no comparison of target charts is needed. The equal-dimensional
case, which needs only first derivatives and allows boundary in the source, is
`TauCeti.isNullSet_image_of_not_isRegularPoint`. Manifolds modelled on Euclidean half-spaces and
Euclidean quadrants are treated in `TauCeti.Geometry.Manifold.Sard.HalfSpace` and
`TauCeti.Geometry.Manifold.Sard.Quadrant`.

## Main results

* `TauCeti.isNullSet_image_of_finrank_lt_finrank`: the image of a differentiable map from a
  manifold of smaller dimension is null.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_isInteriorPoint`: Sard's
  theorem at the sharp regularity `k > m - n`, `k ≥ 1`, for interior critical points of an
  arbitrary manifold with boundary or corners.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_iUnion_range`,
  `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_range`, and
  `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_union_range`:
  reduction of Sard's theorem on a manifold with boundary or corners to boundary parametrizations.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt`: Sard's theorem at the sharp
  regularity `k > m - n`, `k ≥ 1`, for boundaryless manifolds (`[BoundarylessManifold I M]`).
* `ContMDiff.isNullSet_image_criticalPoints` and `ContMDiff.dense_isRegularValue`: the critical
  values of such a map are null, and its regular values are dense.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 and its proof (passage from coordinates to manifolds).
-/

public section

open Function Module Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [LindelofSpace M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [MeasurableSpace E'] [BorelSpace E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {f : M → N} {s : Set M}

section LowDimension

variable [IsManifold I 1 M] [IsManifold J 1 N]

omit [FiniteDimensional ℝ E'] in
/-- **Sard's theorem when the source has smaller dimension.** If the model of `M` has smaller
dimension than the model of `N` and `f` is differentiable at every point of `s`, then `f '' s` is
null in `N`. Both manifolds may have boundary or corners. -/
theorem isNullSet_image_of_finrank_lt_finrank (hdim : finrank ℝ E < finrank ℝ E')
    (hf : ∀ x ∈ s, MDifferentiableAt I J f x) : IsNullSet J (f '' s) := by
  refine isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ μ _ ↦ ?_
  refine DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank μ ?_ hdim
  rintro _ ⟨x, hx, rfl⟩
  refine ((mdifferentiableAt_iff_of_mem_source hx.1.2 hx.2).1 (hf x hx.1.1)).2.mono ?_
  rintro _ ⟨x', -, rfl⟩
  rw [extChartAt_coe]
  exact mem_range_self _

omit [FiniteDimensional ℝ E'] in
/-- The range of a differentiable map from a Lindelöf manifold to a manifold of larger dimension is
null. -/
theorem _root_.MDifferentiable.isNullSet_range_of_finrank_lt_finrank
    (hf : MDifferentiable I J f) (hdim : finrank ℝ E < finrank ℝ E') :
    IsNullSet J (range f) := by
  rw [← image_univ]
  exact isNullSet_image_of_finrank_lt_finrank hdim fun x _ ↦ hf x

end LowDimension

section Interior

variable {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

omit [FiniteDimensional ℝ E] [LindelofSpace M] [FiniteDimensional ℝ E'] [MeasurableSpace E']
  [BorelSpace E'] in
/-- At an interior non-regular point where `f` is `C^n`, `n ≠ 0`, the coordinate expression of `f`
in charts containing the point and its image is `C^n` and has nonsurjective derivative. -/
private theorem contDiffAt_and_not_surjective_fderiv_extChartAt (hn : n ≠ 0) {x₀ x : M} {y₀ : N}
    (hi : I.IsInteriorPoint x) (hf : ContMDiffAt I J n f x) (hreg : ¬ IsRegularPoint I J f x)
    (hx : x ∈ (chartAt H x₀).source) (hfx : f x ∈ (chartAt H' y₀).source) :
    ContDiffAt ℝ n (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ x) ∧
      ¬ Surjective (fderiv ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
        (extChartAt I x₀ x)) := by
  have : IsManifold I 1 M := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold J 1 N := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have hmem : range I ∈ 𝓝 (extChartAt I x₀ x) := Filter.mem_of_superset
    (ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint hn x₀
      (by rwa [extChartAt_source]) hi) (extChartAt_target_subset_range x₀)
  refine ⟨((contMDiffAt_iff_of_mem_source hx hfx).1 hf).2.contDiffAt hmem, ?_⟩
  have h := isRegularPoint_iff_surjective_fderivWithin (hf.mdifferentiableAt hn) hx hfx
  simpa only [fderivWithin_of_mem_nhds hmem] using h.not.mp hreg

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Transfer of a Sard theorem for maps between normed spaces to interior points of manifolds. If
every map `E → E'` that is `C^n` at the points of a set `U` sends the points of `U` where its
derivative is not surjective to a Haar-null set, then the same holds for interior points of a
manifold modelled on `E`. -/
private theorem isNullSet_image_of_forall_addHaar_image_criticalPoints (hn : n ≠ 0)
    (hflat : ∀ (g : E → E') (U : Set E) (μ : Measure E') [μ.IsAddHaarMeasure],
      (∀ z ∈ U, ContDiffAt ℝ n g z) → μ (g '' (U ∩ {z | ¬ Surjective (fderiv ℝ g z)})) = 0)
    (hi : ∀ x ∈ s, I.IsInteriorPoint x) (hf : ∀ x ∈ s, ContMDiffAt I J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  refine isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ μ _ ↦ ?_
  have key : ∀ z ∈ extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source),
      ContDiffAt ℝ n (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z ∧
        ¬ Surjective (fderiv ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z) := by
    rintro _ ⟨x, hx, rfl⟩
    exact contDiffAt_and_not_surjective_fderiv_extChartAt hn (hi x hx.1.1) (hf x hx.1.1)
      (hs x hx.1.1) hx.1.2 hx.2
  refine measure_mono_null (image_mono fun z hz ↦ ?_) (hflat
    (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
    (extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source)) μ
    fun z hz ↦ (key z hz).1)
  exact ⟨hz, (key z hz).2⟩

/-- **Sard's theorem for interior critical points.** Let `M` be a Lindelöf manifold (possibly with
boundary or corners) modelled on a space of dimension `m` and `N` a manifold modelled on a space of
dimension `n`. If `s` consists of interior points of `M` at which `f` is `C^k` with `k > m - n` and
`k ≥ 1` and not regular, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_isInteriorPoint
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hi : ∀ x ∈ s, I.IsInteriorPoint x) (hf : ∀ x ∈ s, ContMDiffAt I J n f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_forall_addHaar_image_criticalPoints
    (fun h ↦ by simp [h] at hk)
    (fun _ _ μ _ hg ↦ addHaar_image_criticalPoints_eq_zero μ hg hk) hi hf hs

/-- **Reduction of Sard's theorem to a countable family of boundary parametrizations.** Suppose that
the boundary points of `M` lying in `s` are covered by the ranges of countably many maps
`g i : B i → M` that are `C^k` on `g i ⁻¹' s`. Since any point `b` over a non-regular point of `f`
is non-regular for `f ∘ g i` (`TauCeti.IsRegularPoint.of_comp`), nullity of `f '' s` reduces to
Sard's theorem for the composites `f ∘ g i` on subsets of `B i`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_iUnion_range
    {ι : Sort*} [Countable ι]
    {Eᵢ : ι → Type*} [∀ i, NormedAddCommGroup (Eᵢ i)] [∀ i, NormedSpace ℝ (Eᵢ i)]
    {Hᵢ : ι → Type*} [∀ i, TopologicalSpace (Hᵢ i)]
    {K : ∀ i, ModelWithCorners ℝ (Eᵢ i) (Hᵢ i)}
    {B : ι → Type*} [∀ i, TopologicalSpace (B i)] [∀ i, ChartedSpace (Hᵢ i) (B i)]
    {g : ∀ i, B i → M}
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (hcover : s ∩ I.boundary M ⊆ ⋃ i, range (g i))
    (hg : ∀ i, ∀ b ∈ g i ⁻¹' s, ContMDiffAt (K i) I n (g i) b)
    (hbd : ∀ (i : ι) (t : Set (B i)),
      (∀ b ∈ t, ContMDiffAt (K i) J n (f ∘ g i) b) →
      (∀ b ∈ t, ¬ IsRegularPoint (K i) J (f ∘ g i) b) →
      IsNullSet J ((f ∘ g i) '' t)) :
    IsNullSet J (f '' s) := by
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have hsub : f '' s ⊆
      f '' {x ∈ s | I.IsInteriorPoint x} ∪ ⋃ i, (f ∘ g i) '' (g i ⁻¹' s) := by
    rintro _ ⟨x, hx, rfl⟩
    rcases I.isInteriorPoint_or_isBoundaryPoint x with hi | hxb
    · exact Or.inl ⟨x, ⟨hx, hi⟩, rfl⟩
    · obtain ⟨i, b, rfl⟩ := mem_iUnion.1 (hcover ⟨hx, hxb⟩)
      exact Or.inr (mem_iUnion.2 ⟨i, b, hx, rfl⟩)
  refine ((isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_isInteriorPoint
    (s := {x ∈ s | I.IsInteriorPoint x}) hk
    (fun _ hx ↦ hx.2) (fun x hx ↦ hf x hx.1) (fun x hx ↦ hs x hx.1)).union
    (IsNullSet.iUnion fun i ↦ hbd i (g i ⁻¹' s)
      (fun b hb ↦ (hf (g i b) hb).comp b (hg i b hb)) fun b hb hreg ↦
        hs (g i b) hb (hreg.of_comp ((hf (g i b) hb).mdifferentiableAt hn)
          ((hg i b hb).mdifferentiableAt hn)))).mono hsub

/-- **Reduction of Sard's theorem to a single boundary parametrization.** If the boundary points of
`M` lying in `s` are covered by the range of a map `g : B → M` that is `C^k` on `g ⁻¹' s`, then
nullity of `f '' s` reduces to Sard's theorem for `f ∘ g` on subsets of `B`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_range
    {E₀ : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    {H₀ : Type*} [TopologicalSpace H₀] {K : ModelWithCorners ℝ E₀ H₀}
    {B : Type*} [TopologicalSpace B] [ChartedSpace H₀ B] {g : B → M}
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (hcover : s ∩ I.boundary M ⊆ range g)
    (hg : ∀ b ∈ g ⁻¹' s, ContMDiffAt K I n g b)
    (hbd : ∀ t : Set B,
      (∀ b ∈ t, ContMDiffAt K J n (f ∘ g) b) →
      (∀ b ∈ t, ¬ IsRegularPoint K J (f ∘ g) b) →
      IsNullSet J ((f ∘ g) '' t)) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_iUnion_range
    (ι := Unit) (K := fun _ ↦ K) (g := fun _ ↦ g) hk hf hs
    (hcover.trans fun _ hx ↦ mem_iUnion.2 ⟨(), hx⟩) (fun _ ↦ hg) (fun _ ↦ hbd)

/-- **Reduction of Sard's theorem to two boundary parametrizations.** If the boundary points of `M`
lying in `s` are covered by the union of the ranges of two maps `g₁ : B₁ → M` and `g₂ : B₂ → M`
that are `C^k` on the preimages of `s`, then nullity of `f '' s` reduces to Sard's theorem for
`f ∘ g₁` and `f ∘ g₂`. This is the form used for products `M₁ × M₂`, whose boundary is
`(univ ×ˢ ∂M₂) ∪ (∂M₁ ×ˢ univ)`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_boundary_subset_union_range
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    {H₁ : Type*} [TopologicalSpace H₁] {K₁ : ModelWithCorners ℝ E₁ H₁}
    {B₁ : Type*} [TopologicalSpace B₁] [ChartedSpace H₁ B₁] {g₁ : B₁ → M}
    {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    {H₂ : Type*} [TopologicalSpace H₂] {K₂ : ModelWithCorners ℝ E₂ H₂}
    {B₂ : Type*} [TopologicalSpace B₂] [ChartedSpace H₂ B₂] {g₂ : B₂ → M}
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x)
    (hcover : s ∩ I.boundary M ⊆ range g₁ ∪ range g₂)
    (hg₁ : ∀ b ∈ g₁ ⁻¹' s, ContMDiffAt K₁ I n g₁ b)
    (hg₂ : ∀ b ∈ g₂ ⁻¹' s, ContMDiffAt K₂ I n g₂ b)
    (hbd₁ : ∀ t : Set B₁,
      (∀ b ∈ t, ContMDiffAt K₁ J n (f ∘ g₁) b) →
      (∀ b ∈ t, ¬ IsRegularPoint K₁ J (f ∘ g₁) b) →
      IsNullSet J ((f ∘ g₁) '' t))
    (hbd₂ : ∀ t : Set B₂,
      (∀ b ∈ t, ContMDiffAt K₂ J n (f ∘ g₂) b) →
      (∀ b ∈ t, ¬ IsRegularPoint K₂ J (f ∘ g₂) b) →
      IsNullSet J ((f ∘ g₂) '' t)) :
    IsNullSet J (f '' s) := by
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have hsub : f '' s ⊆ f '' {x ∈ s | I.IsInteriorPoint x} ∪
      ((f ∘ g₁) '' (g₁ ⁻¹' s) ∪ (f ∘ g₂) '' (g₂ ⁻¹' s)) := by
    rintro _ ⟨x, hx, rfl⟩
    rcases I.isInteriorPoint_or_isBoundaryPoint x with hi | hxb
    · exact Or.inl ⟨x, ⟨hx, hi⟩, rfl⟩
    · rcases hcover ⟨hx, hxb⟩ with ⟨b, rfl⟩ | ⟨b, rfl⟩
      · exact Or.inr (Or.inl ⟨b, hx, rfl⟩)
      · exact Or.inr (Or.inr ⟨b, hx, rfl⟩)
  refine ((isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_isInteriorPoint
    (s := {x ∈ s | I.IsInteriorPoint x}) hk
    (fun _ hx ↦ hx.2) (fun x hx ↦ hf x hx.1) (fun x hx ↦ hs x hx.1)).union
    ((hbd₁ (g₁ ⁻¹' s) (fun b hb ↦ (hf (g₁ b) hb).comp b (hg₁ b hb)) fun b hb hreg ↦
        hs (g₁ b) hb (hreg.of_comp ((hf (g₁ b) hb).mdifferentiableAt hn)
          ((hg₁ b hb).mdifferentiableAt hn))).union
      (hbd₂ (g₂ ⁻¹' s) (fun b hb ↦ (hf (g₂ b) hb).comp b (hg₂ b hb)) fun b hb hreg ↦
        hs (g₂ b) hb (hreg.of_comp ((hf (g₂ b) hb).mdifferentiableAt hn)
          ((hg₂ b hb).mdifferentiableAt hn))))).mono hsub

end Interior

section Boundaryless

variable [BoundarylessManifold I M] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- **Sard's theorem.** Let `M` be a boundaryless Lindelöf manifold modelled on a space of
dimension `m` and `N` a manifold modelled on a space of dimension `n`. If `f` is `C^k` at every
point of `s` with `k > m - n` and `k ≥ 1`, and no point of `s` is regular, then `f '' s` is null in
`N`. This is the sharp regularity of Sard's theorem. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt_of_isInteriorPoint hk
    (fun _ _ ↦ BoundarylessManifold.isInteriorPoint) hf hs

/-- **Sard's theorem.** The critical values of a `C^k` map from a boundaryless Lindelöf manifold
of dimension `m` to a manifold of dimension `n` form a null set when `k > m - n` and `k ≥ 1`, in
particular when the map is smooth. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt hk (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map from a boundaryless Lindelöf manifold of dimension `m` to a
manifold of dimension `n` are dense when `k > m - n` and `k ≥ 1`, in particular when the map is
smooth. -/
theorem _root_.ContMDiff.dense_isRegularValue (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints hk).dense_compl

end Boundaryless

end TauCeti
