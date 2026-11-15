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
so it applies to maps that are only defined, or only regular, on an open subset of `M`. In the
second case, the points of `s` are interior points of `M` (`ModelWithCorners.IsInteriorPoint`); in
particular this covers every boundaryless manifold `M`, even when its model with corners `I` has
boundary, and reduces Sard's theorem on any manifold with boundary or corners to the boundary points
of `s` (`TauCeti.isNullSet_image_iff_inter_boundary`). For manifolds modelled on the half-space or
the quadrant, see `TauCeti.Geometry.Manifold.Sard.Boundary`.

The proofs read `f` in pairs of extended charts and apply the corresponding theorem for maps
between normed spaces (`TauCeti.addHaar_image_criticalPoints_eq_zero` and
`DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank`). A countable family of charts
covers `M` (`TauCeti.isNullSet_image_of_forall_addHaar_image_extChartAt`), and since nullity is
tested in every chart of `N`, no comparison of target charts is needed. The equal-dimensional
case, which needs only first derivatives and allows boundary in the source, is
`TauCeti.isNullSet_image_of_not_isRegularPoint`.

## Main results

* `TauCeti.isNullSet_image_of_finrank_lt_finrank`: the image of a differentiable map from a
  manifold of smaller dimension is null.
* `TauCeti.isNullSet_image_iff_inter_boundary`: when `f` is `C^k` (`k > m - n`, `k ≥ 1`) and
  non-regular at the interior points of `s`, `f '' s` is null if and only if
  `f '' (s ∩ I.boundary M)` is null.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt`: Sard's theorem at the sharp
  regularity `k > m - n`, `k ≥ 1`, for boundaryless manifolds in arbitrary dimensions.
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
  have hnhds : range I ∈ 𝓝 (extChartAt I x₀ x) :=
    Filter.mem_of_superset (mem_interior_iff_mem_nhds.1
      ((I.isInteriorPoint_iff_of_mem_atlas one_ne_zero (chart_mem_atlas H x₀) hx).1 hi))
      (extChartAt_target_subset_range x₀)
  refine ⟨((contMDiffAt_iff_of_mem_source hx hfx).1 hf).2.contDiffAt hnhds, ?_⟩
  exact (isRegularPoint_iff_surjective_fderiv_extChartAt_of_isInteriorPoint hi
    (hf.mdifferentiableAt hn) hx hfx).not.mp hreg

/-- **Reduction of Sard's theorem to the boundary.** Let `M` be a Lindelöf manifold modelled on a
space of dimension `m` and `N` a manifold modelled on a space of dimension `n`, with `k > m - n` and
`k ≥ 1`. If at every interior point of `M` lying in `s` the map `f` is `C^k` and non-regular, then
`f '' s` is null in `N` if and only if `f '' (s ∩ I.boundary M)` is null in `N`. -/
theorem isNullSet_image_iff_inter_boundary
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, I.IsInteriorPoint x → ContMDiffAt I J n f x)
    (hs : ∀ x ∈ s, I.IsInteriorPoint x → ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) ↔ IsNullSet J (f '' (s ∩ I.boundary M)) := by
  refine ⟨fun h ↦ h.mono (image_mono inter_subset_left), fun hbdry ↦ ?_⟩
  have hn : n ≠ 0 := fun h ↦ by simp [h] at hk
  have hsplit : s = s ∩ I.interior M ∪ s ∩ I.boundary M := by
    rw [← inter_union_distrib_left, I.interior_union_boundary_eq_univ, inter_univ]
  rw [hsplit, image_union]
  refine (isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ μ _ ↦ ?_).union
    hbdry
  have key : ∀ z ∈ extChartAt I x₀ ''
        ((s ∩ I.interior M) ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source),
      ContDiffAt ℝ n (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z ∧
        ¬ Surjective (fderiv ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z) := by
    rintro _ ⟨x, hx, rfl⟩
    exact contDiffAt_and_not_surjective_fderiv_extChartAt hn hx.1.1.2 (hf x hx.1.1.1 hx.1.1.2)
      (hs x hx.1.1.1 hx.1.1.2) hx.1.2 hx.2
  refine measure_mono_null (image_mono ?_)
    (addHaar_image_criticalPoints_eq_zero μ (fun z hz ↦ (key z hz).1) hk)
  exact fun z hz ↦ ⟨hz, (key z hz).2⟩

end Interior

section Boundaryless

variable [BoundarylessManifold I M] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

/-- **Sard's theorem.** Let `M` be a boundaryless Lindelöf manifold modelled on a space of
dimension `m` and `N` a manifold modelled on a space of dimension `n`. If `f` is `C^k` at every
point of `s` with `k > m - n` and `k ≥ 1`, and no point of `s` is regular, then `f '' s` is null in
`N`. This is the sharp regularity of Sard's theorem; the model `I` itself may have boundary or
corners. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  rw [isNullSet_image_iff_inter_boundary hk (fun x hx _ ↦ hf x hx) (fun x hx _ ↦ hs x hx),
    ModelWithCorners.Boundaryless.boundary_eq_empty, inter_empty, image_empty]
  exact (isNullSet_iff J ∅).2 fun _ _ _ ↦ by simp

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
