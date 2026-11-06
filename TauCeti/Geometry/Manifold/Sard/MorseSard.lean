/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.RegularValue.Open
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Analysis.Calculus.Sard.OutermostStratum

/-!
# The Morse–Sard theorem on manifolds

Let `f : M → N` be a `C^k` map between real manifolds modelled on finite-dimensional spaces of
dimensions `m` and `n`, where `M` has no boundary and is Lindelöf (for instance second countable).
If `k ≥ m² + 1`, the critical values of `f` form a null set of `N`: in every extended chart of `N`
their image has Haar measure zero. The regular values of `f` are therefore dense. When
`m ≤ n + 2` the same holds at Sard's sharp regularity `k > max (m - n) 0`. The dimensions are
otherwise unrelated, and either of them may be zero. Nullity in `N` is
`TauCeti.IsNullSet`, read through charts, so no measure on `N` is chosen.

These are the manifold forms of the flat theorems
`TauCeti.addHaar_image_criticalPoints_eq_zero` and
`TauCeti.addHaar_image_criticalPoints_eq_zero_of_finrank_le_add_two`. Read in a pair of extended
charts, `f` becomes a `C^k` map between the models whose critical points are the chart images of
those of `f` (`TauCeti.isRegularPoint_iff_surjective_fderivWithin`), and the flat theorem applies
on the set of chart images, which need not be open. Countably many source charts cover `M` by the
Lindelöf property, and null sets are closed under countable unions. Only the source needs to be
boundaryless: there `C^k` in the manifold sense is `C^k` of the coordinate expression at
interior points. The target may have boundary or corners.

The set forms take a set `s` of critical points at which `f` is `C^k`, so they apply to maps
defined or smooth only on an open subset of `M`. Equal dimensions need only differentiability and
allow boundary in the source; that case is `TauCeti.isNullSet_image_criticalPoints`.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_contMDiffAt`: the image of a set of critical
  points at which `f` is `C^(m² + 1)` is null.
* `TauCeti.isNullSet_image_of_not_isRegularPoint_of_finrank_le_add_two`: the same at the sharp
  regularity, when `m ≤ n + 2`.
* `ContMDiff.isNullSet_image_criticalPoints`: **the Morse–Sard theorem on manifolds**.
* `ContMDiff.isNullSet_image_criticalPoints_of_finrank_le_add_two`: its sharp form in codimension
  at most two.
* `ContMDiff.dense_isRegularValue` and `ContMDiff.dense_isRegularValue_of_finrank_le_add_two`:
  the regular values are dense.

## References

* A. Sard, *The measure of the critical values of differentiable maps*, Bull. Amer. Math. Soc.
  **48** (1942), 883–890.
* J. Milnor, *Topology from the differentiable viewpoint*, University Press of Virginia, 1965, §2
  and §3.
* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10 (the chart transfer).
-/

public section

open Function Module Set MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : ℕ∞ω} [IsManifold I n M] [IsManifold J n N]
  {f : M → N} {s : Set M}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- The chart transfer of a flat Sard theorem `hflat` at regularity `n`. -/
private theorem isNullSet_image_of_not_isRegularPoint_of_flat [LindelofSpace M]
    [MeasurableSpace E'] [BorelSpace E'] (hn : 1 ≤ n)
    (hflat : ∀ (g : E → E') (U : Set E), (∀ z ∈ U, ContDiffAt ℝ n g z) →
      ∀ (μ : Measure E') [μ.IsAddHaarMeasure],
        μ (g '' (U ∩ {z | ¬ Surjective (fderiv ℝ g z)})) = 0)
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  have : IsManifold I 1 M := IsManifold.of_le hn
  have : IsManifold J 1 N := IsManifold.of_le hn
  refine isNullSet_image_of_forall_extChartAt (I := I) fun x₀ y₀ μ _ ↦ ?_
  refine measure_mono_null (image_mono (subset_inter subset_rfl ?_)) (hflat _ _ ?_ μ)
  · -- Every chart image of a point of `s` is a critical point of the coordinate expression.
    rintro _ ⟨x, hx, rfl⟩
    have h := isRegularPoint_iff_surjective_fderivWithin
      ((hf x hx.1.1).mdifferentiableAt (by positivity)) hx.1.2 hx.2
    simpa only [I.range_eq_univ, fderivWithin_univ, mem_ofPred_eq] using h.not.mp (hs x hx.1.1)
  · -- Without boundary, `C^n` in the manifold sense is `C^n` of the coordinate expression.
    rintro _ ⟨x, hx, rfl⟩
    exact ((contMDiffAt_iff_of_mem_source hx.1.2 hx.2).1 (hf x hx.1.1)).2.contDiffAt
      (by simp [I.range_eq_univ])

/-- **The Morse–Sard theorem on manifolds**, for a set of critical points. Let `M` be a Lindelöf
manifold without boundary modelled on a space of dimension `m`, and `N` a manifold modelled on a
finite-dimensional space. If `f` is `C^n` with `m² + 1 ≤ n` at every point of `s` and no point of
`s` is regular, then `f '' s` is null in `N`. The set `s` need not be open. -/
theorem isNullSet_image_of_not_isRegularPoint_of_contMDiffAt [LindelofSpace M]
    [MeasurableSpace E'] [BorelSpace E']
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x)
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_flat (le_trans (by exact_mod_cast Nat.le_add_left _ _)
    hk) (fun _ _ hg μ _ ↦ addHaar_image_criticalPoints_eq_zero μ hg hk) hf hs

/-- **The Morse–Sard theorem on manifolds at the sharp regularity, in codimension at most two**,
for a set of critical points. Let `M` be a Lindelöf manifold without boundary modelled on a space
of dimension `m`, and `N` a manifold modelled on a space of dimension `n'` with `m ≤ n' + 2`. If
`f` is `C^n` with `m - n' < n` at every point of `s` and no point of `s` is regular, then
`f '' s` is null in `N`. The set `s` need not be open. -/
theorem isNullSet_image_of_not_isRegularPoint_of_finrank_le_add_two [LindelofSpace M]
    [MeasurableSpace E'] [BorelSpace E']
    (hf : ∀ x ∈ s, ContMDiffAt I J n f x) (hcodim : finrank ℝ E ≤ finrank ℝ E' + 2)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) :=
  isNullSet_image_of_not_isRegularPoint_of_flat (le_trans (by exact_mod_cast Nat.le_add_left _ _)
    hk) (fun _ _ hg μ _ ↦ addHaar_image_criticalPoints_eq_zero_of_finrank_le_add_two μ hg hcodim hk)
    hf hs

/-- **The Morse–Sard theorem on manifolds.** The critical values of a `C^n` map from a Lindelöf
manifold without boundary modelled on a space of dimension `m` to a manifold with a
finite-dimensional model form a null set, provided `m² + 1 ≤ n`. No relation between the two
dimensions is required. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints [LindelofSpace M] [MeasurableSpace E']
    [BorelSpace E'] (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_contMDiffAt (fun x _ ↦ hf x) hk fun _ hx ↦ hx

/-- **The Morse–Sard theorem on manifolds at the sharp regularity, in codimension at most two.**
The critical values of a `C^n` map from a Lindelöf manifold without boundary modelled on a space
of dimension `m` to a manifold modelled on a space of dimension `n'` form a null set, provided
`m ≤ n' + 2` and `m - n' < n`. -/
theorem _root_.ContMDiff.isNullSet_image_criticalPoints_of_finrank_le_add_two [LindelofSpace M]
    [MeasurableSpace E'] [BorelSpace E'] (hf : ContMDiff I J n f)
    (hcodim : finrank ℝ E ≤ finrank ℝ E' + 2)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint_of_finrank_le_add_two (fun x _ ↦ hf x) hcodim hk
    fun _ hx ↦ hx

/-- The regular values of a `C^n` map from a Lindelöf manifold without boundary modelled on a
space of dimension `m` to a manifold with a finite-dimensional model are dense, provided
`m² + 1 ≤ n`. -/
theorem _root_.ContMDiff.dense_isRegularValue [LindelofSpace M] (hf : ContMDiff I J n f)
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints hk).dense_compl

/-- The regular values of a `C^n` map from a Lindelöf manifold without boundary modelled on a
space of dimension `m` to a manifold modelled on a space of dimension `n'` are dense, provided
`m ≤ n' + 2` and `m - n' < n`. -/
theorem _root_.ContMDiff.dense_isRegularValue_of_finrank_le_add_two [LindelofSpace M]
    (hf : ContMDiff I J n f) (hcodim : finrank ℝ E ≤ finrank ℝ E' + 2)
    (hk : ((finrank ℝ E - finrank ℝ E' + 1 : ℕ) : ℕ∞ω) ≤ n) :
    Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (hf.isNullSet_image_criticalPoints_of_finrank_le_add_two hcodim hk).dense_compl

end TauCeti
