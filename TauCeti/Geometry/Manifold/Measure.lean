/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Null sets on manifolds

This file defines chartwise nullity for subsets of a charted manifold, without installing a
measurable structure on the manifold itself.  The definition is independent of the choice of Haar
measure on the model and has the usual subset and finite-union closure properties.
-/

public section

open Set
open MeasureTheory
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]

/-- A set is null on a manifold when its image in every extended chart is null for every Haar
measure on the model.  This definition needs no measurable structure on the manifold itself. -/
def IsNullSet (I : ModelWithCorners ℝ E H) [MeasurableSpace E] [hE : BorelSpace E]
    (s : Set M) : Prop :=
  let _ : BorelSpace E := hE
  ∀ x : M, ∀ (μ : Measure E) [μ.IsAddHaarMeasure],
    μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0

/-- The chartwise characterization of `IsNullSet`. -/
theorem isNullSet_iff (I : ModelWithCorners ℝ E H) [MeasurableSpace E] [hE : BorelSpace E]
    (s : Set M) :
    IsNullSet I s ↔ ∀ x : M, ∀ (μ : Measure E) [μ.IsAddHaarMeasure],
      μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0 := by
  rfl

/-- The chartwise nullity statement for a null set at a point and Haar measure. -/
theorem IsNullSet.chartwise {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {s : Set M} (hs : IsNullSet I s) (x : M) (μ : Measure E) [μ.IsAddHaarMeasure] :
    μ (extChartAt I x '' (s ∩ (extChartAt I x).source)) = 0 :=
  (isNullSet_iff I s).1 hs x μ

/-- A subset of a null set is null. -/
theorem IsNullSet.mono {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {s t : Set M} (ht : IsNullSet I t) (hst : s ⊆ t) : IsNullSet I s := by
  rw [isNullSet_iff] at ht ⊢
  intro x μ hμ
  apply measure_mono_null _ (ht x μ)
  exact image_mono (inter_subset_inter_left _ hst)

/-- The union of two null sets is null. -/
theorem IsNullSet.union {I : ModelWithCorners ℝ E H} [MeasurableSpace E] [hE : BorelSpace E]
    {s t : Set M} (hs : IsNullSet I s) (ht : IsNullSet I t) : IsNullSet I (s ∪ t) := by
  rw [isNullSet_iff] at hs ht ⊢
  intro x μ hμ
  rw [union_inter_distrib_right, image_union]
  exact measure_union_null (hs x μ) (ht x μ)

end TauCeti
