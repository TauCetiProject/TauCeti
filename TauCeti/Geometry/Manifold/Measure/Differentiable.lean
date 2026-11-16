/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.MeasureTheory.Measure.Haar.Differentiable

/-!
# Differentiable images of null sets on manifolds

Let `M` and `N` be real manifolds, possibly with boundary or corners, modelled on
finite-dimensional spaces `E` and `F` with `finrank ℝ E ≤ finrank ℝ F`, and let `M` be Lindelöf.
A map `g : M → N` that is differentiable within a null set `A` of `M` sends it to a null set of
`N`. No measurable structure on `M` or `N` and no measurability of `A` is needed.

In charts this is `DifferentiableOn.addHaar_image_eq_zero`, and nullity of an image is read in
charts by `TauCeti.isNullSet_image_of_forall_addHaar_image_extChartAt`.

A finite-dimensional real normed space, seen as a manifold modelled on itself, has as null sets
exactly the sets that are null for an additive Haar measure, since any two additive Haar measures
are mutually absolutely continuous. This lets maps from or to a normed space be treated in the same
way.

## Main results

* `TauCeti.isNullSet_modelWithCornersSelf_iff`: in a finite-dimensional real normed space, null
  sets are the Haar-null sets.
* `TauCeti.IsNullSet.image_of_mdifferentiableOn`: a map differentiable within a null set sends
  it to a null set, when the dimension of the source is at most that of the target.
-/

public section

open MeasureTheory Module Set
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] [LindelofSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {g : M → N} {A : Set M}

/-- A subset of a finite-dimensional real normed space, seen as a manifold modelled on itself, is
null exactly when it is null for an additive Haar measure. -/
theorem isNullSet_modelWithCornersSelf_iff (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} :
    IsNullSet 𝓘(ℝ, E) s ↔ μ s = 0 := by
  refine ⟨fun hs ↦ by simpa [extChartAt_model_space_eq_id] using hs.chartwise 0 μ,
    fun hs ↦ (isNullSet_iff _ _).2 fun x ν _ ↦ ?_⟩
  simpa [extChartAt_model_space_eq_id] using Measure.absolutelyContinuous_isAddHaarMeasure ν μ hs

/-- **Differentiable maps preserve null sets.** Let `M` be Lindelöf, with model of dimension at
most that of the model of `N`. If `g : M → N` is differentiable within a null set `A`, then
`g '' A` is null. -/
theorem IsNullSet.image_of_mdifferentiableOn (hA : IsNullSet I A)
    (hdim : finrank ℝ E ≤ finrank ℝ F) (hg : MDifferentiableOn I J g A) :
    IsNullSet J (g '' A) := by
  refine isNullSet_image_of_forall_addHaar_image_extChartAt (I := I) fun x₀ y₀ ν _ ↦ ?_
  refine DifferentiableOn.addHaar_image_eq_zero (Basis.addHaar (finBasis ℝ E)) ν hdim ?_ ?_
  · exact ((mdifferentiableOn_iff_of_subset_source (s := A ∩ _ ∩ g ⁻¹' _) (fun _ hx ↦ hx.1.2)
      fun _ hx ↦ hx.2).1 (hg.mono fun _ hx ↦ hx.1.1)).2
  · refine measure_mono_null (image_mono ?_) (hA.chartwise x₀ (finBasis ℝ E).addHaar)
    rintro x ⟨⟨hxA, hxsrc⟩, -⟩
    exact ⟨hxA, by rwa [extChartAt_source]⟩

end TauCeti
