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
import TauCeti.Analysis.Calculus.Sard.Scalar

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
* If `m ≤ n + 2`, a `C^k` map with `k > m - n` suffices. This is the sharp regularity of Sard's
  theorem: Whitney's example shows that a `C¹` function on the plane can have critical values of
  positive measure.
* In general, a `C^k` map with `k ≥ m² + 1` suffices, in particular a smooth map.
* For a real-valued map, `k ≥ m` and `k ≥ 1` suffice in every source dimension.

Each statement only asks for the regularity at the points of a given set `s` of critical points,
so it applies to maps that are only defined, or only regular, on an open subset of `M`. Except in
the first case, `M` is boundaryless, in the sense that its model fills `E`.

The proofs read `f` in pairs of extended charts and apply the corresponding theorem for maps
between normed spaces (`TauCeti.addHaar_image_criticalPoints_eq_zero_of_finrank_le_add_two`,
`TauCeti.addHaar_image_criticalPoints_eq_zero` and
`DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank`). A countable family of charts
covers `M` (`TauCeti.isNullSet_image_of_forall_addHaar_image_extChartAt`), and since nullity is
tested in every chart of `N`, no comparison of target charts is needed. The equal-dimensional
case, which needs only first derivatives and allows boundary in the source, is
`TauCeti.isNullSet_image_of_not_isRegularPoint`.

## Main results

* `TauCeti.isNullSet_image_of_finrank_lt_finrank`: the image of a differentiable map from a
  manifold of smaller dimension is null.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_finrank_le_add_two`: Sard's theorem at the
  sharp regularity in codimension at most two.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt`: Sard's theorem at regularity
  `m² + 1`, for arbitrary dimensions.
* `ContMDiff.isNullSet_image_criticalPoints` and `ContMDiff.dense_isRegularValue`: the critical
  values of a smooth map are null, and its regular values are dense.
* `ContMDiff.isNullSet_image_criticalPoints_of_real` and
  `ContMDiff.dense_isRegularValue_of_real`: the scalar forms at regularity `max 1 m`.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  48 (1942), 883–890.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 and its proof (passage from coordinates to manifolds).
-/

public section

open Function Module Set MeasureTheory
open scoped Manifold ContDiff

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

/-- The range of a differentiable map from a Lindelöf manifold to a manifold of larger dimension is
null. -/
theorem _root_.MDifferentiable.isNullSet_range_of_finrank_lt_finrank
    (hf : MDifferentiable I J f) (hdim : finrank ℝ E < finrank ℝ E') :
    IsNullSet J (range f) := by
  rw [← image_univ]
  exact isNullSet_image_of_finrank_lt_finrank hdim fun x _ ↦ hf x

end LowDimension

section Boundaryless

variable [I.Boundaryless] {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]

omit [FiniteDimensional ℝ E] [LindelofSpace M] [FiniteDimensional ℝ E'] [MeasurableSpace E']
  [BorelSpace E'] in
/-- At a non-regular point where `f` is `C^n`, `n ≠ 0`, the coordinate expression of `f` in charts
containing the point and its image is `C^n` and has nonsurjective derivative. -/
private theorem contDiffAt_and_not_surjective_fderiv_extChartAt (hn : n ≠ 0) {x₀ x : M} {y₀ : N}
    (hf : ContMDiffAt I J n f x) (hreg : ¬ IsRegularPoint I J f x)
    (hx : x ∈ (chartAt H x₀).source) (hfx : f x ∈ (chartAt H' y₀).source) :
    ContDiffAt ℝ n (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) (extChartAt I x₀ x) ∧
      ¬ Surjective (fderiv ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
        (extChartAt I x₀ x)) := by
  have : IsManifold I 1 M := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  have : IsManifold J 1 N := .of_le (ENat.one_le_iff_ne_zero_withTop.2 hn)
  refine ⟨((contMDiffAt_iff_of_mem_source hx hfx).1 hf).2.contDiffAt
    (by simp [I.range_eq_univ]), ?_⟩
  have h := isRegularPoint_iff_surjective_fderivWithin (hf.mdifferentiableAt hn) hx hfx
  simpa only [I.range_eq_univ, fderivWithin_univ] using h.not.mp hreg

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Transfer of a Sard theorem for maps between normed spaces to manifolds. If every map `E → E'`
that is `C^n` at the points of a set `U` sends the points of `U` where its derivative is not
surjective to a Haar-null set, then the same holds for maps between manifolds modelled on `E` and
`E'`. -/
private theorem isNullSet_image_of_forall_addHaar_image_criticalPoints (hn : n ≠ 0)
    (hflat : ∀ (g : E → E') (U : Set E) (μ : Measure E') [μ.IsAddHaarMeasure],
      (∀ z ∈ U, ContDiffAt ℝ n g z) → μ (g '' (U ∩ {z | ¬ Surjective (fderiv ℝ g z)})) = 0)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  refine isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ μ _ ↦ ?_
  have key : ∀ z ∈ extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source),
      ContDiffAt ℝ n (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z ∧
        ¬ Surjective (fderiv ℝ (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm) z) := by
    rintro _ ⟨x, hx, rfl⟩
    exact contDiffAt_and_not_surjective_fderiv_extChartAt hn (hf x hx.1.1) (hs x hx.1.1)
      hx.1.2 hx.2
  refine measure_mono_null (image_mono fun z hz ↦ ?_) (hflat
    (extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm)
    (extChartAt I x₀ '' (s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source)) μ
    fun z hz ↦ (key z hz).1)
  exact ⟨hz, (key z hz).2⟩

/-- **Sard's theorem at the sharp regularity, in codimension at most two.** Let `M` be a
boundaryless Lindelöf manifold modelled on a space of dimension `m` and `N` a manifold modelled on
a space of dimension `n`, with `m ≤ n + 2`. If `f` is `C^k` at every point of `s` with `k > m - n`,
and no point of `s` is regular, then `f '' s` is null in `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_finrank_le_add_two
    (hcodim : finrank ℝ E ≤ finrank ℝ E' + 2)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_forall_addHaar_image_criticalPoints
    (fun h ↦ by simp [h] at hk)
    (fun _ _ μ _ hg ↦ addHaar_image_criticalPoints_eq_zero_of_finrank_le_add_two μ hg hcodim hk)
    hf hs

/-- **Sard's theorem at the sharp regularity, in codimension at most two.** The critical values
of a `C^k` map from a boundaryless Lindelöf manifold of dimension `m` to a manifold of dimension
`n ≥ m - 2` form a null set when `k > m - n`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_finrank_le_add_two
    (hf : ContMDiff I J n f) (hcodim : finrank ℝ E ≤ finrank ℝ E' + 2)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_finrank_le_add_two hcodim hk
    (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a `C^k` map from a boundaryless Lindelöf manifold of dimension `m` to a
manifold of dimension `n ≥ m - 2` are dense when `k > m - n`. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_finrank_le_add_two
    (hf : ContMDiff I J n f) (hcodim : finrank ℝ E ≤ finrank ℝ E' + 2)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_of_finrank_le_add_two hcodim hk).dense_compl

/-- **Sard's theorem in arbitrary dimensions.** Let `M` be a boundaryless Lindelöf manifold
modelled on a space of dimension `m`. If `f` is `C^k` at every point of `s` with `k ≥ m² + 1`, and
no point of `s` is regular, then `f '' s` is null in `N`, whatever the dimension of `N`. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_forall_addHaar_image_criticalPoints
    (fun h ↦ by simp [h] at hk)
    (fun _ _ μ _ hg ↦ addHaar_image_criticalPoints_eq_zero μ hg hk) hf hs

/-- **Sard's theorem for smooth maps.** The critical values of a smooth map from a boundaryless
Lindelöf manifold with finite-dimensional model to a manifold with finite-dimensional model form
a null set. The dimensions may differ. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints (hf : ContMDiff I J n f) (hn : ∞ ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt
    (le_trans (by exact_mod_cast le_top) hn) (fun x _ ↦ hf x) fun _ hx ↦ hx

omit [MeasurableSpace E'] [BorelSpace E'] in
/-- The regular values of a smooth map from a boundaryless Lindelöf manifold with
finite-dimensional model to a manifold with finite-dimensional model are dense. -/
theorem _root_.ContMDiff.dense_isRegularValue (hf : ContMDiff I J n f) (hn : ∞ ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints hn).dense_compl

end Boundaryless

section Scalar

variable [I.Boundaryless] {n : ℕ∞ω} [IsManifold I n M] {g : M → ℝ}

/-- **Scalar Morse--Sard on a manifold.** A real-valued map that is `C^n` at each point of a
set of critical points has null image, if `n ≠ 0` and `finrank ℝ E ≤ n`. The source is a
boundaryless Lindelöf manifold. No measurability or openness assumption on the set is needed. -/
theorem isNullSet_image_of_not_isRegularPoint_of_real (hn : n ≠ 0)
    (hk : (finrank ℝ E : ℕ∞ω) ≤ n)
    (hg : ∀ x ∈ s, ContMDiffAt I 𝓘(ℝ, ℝ) n g x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I 𝓘(ℝ, ℝ) g x) :
    IsNullSet 𝓘(ℝ, ℝ) (g '' s) :=
  isNullSet_image_of_forall_addHaar_image_criticalPoints hn
    (fun _ _ μ _ hf ↦ addHaar_image_criticalPoints_eq_zero_of_real μ hf hk) hg hs

/-- The critical values of a real-valued `C^n` map on a boundaryless Lindelöf manifold are
null when `n ≠ 0` and the source dimension is at most `n`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_real
    (hg : ContMDiff I 𝓘(ℝ, ℝ) n g) (hn : n ≠ 0) (hk : (finrank ℝ E : ℕ∞ω) ≤ n) :
    IsNullSet 𝓘(ℝ, ℝ) (g '' {x | ¬ IsRegularPoint I 𝓘(ℝ, ℝ) g x}) :=
  isNullSet_image_of_not_isRegularPoint_of_real hn hk (fun x _ ↦ hg x) fun _ hx ↦ hx

/-- The regular values of a real-valued `C^n` map on a boundaryless Lindelöf manifold are
dense when `n ≠ 0` and the source dimension is at most `n`. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_real
    (hg : ContMDiff I 𝓘(ℝ, ℝ) n g) (hn : n ≠ 0) (hk : (finrank ℝ E : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I 𝓘(ℝ, ℝ) g y} := by
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hg.isNullSet_image_criticalPoints_of_real hn hk).dense_compl

end Scalar

end TauCeti
