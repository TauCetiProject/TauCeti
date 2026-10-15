/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import TauCeti.Topology.Connected.EMetricSpace
public import TauCeti.Topology.EMetricSpace.Lipschitz

/-!
# Hausdorff length of preconnected sets

The distance between two points of a preconnected set is bounded by its one-dimensional
Hausdorff measure. Taking the supremum over both points bounds the extended diameter. These
estimates turn the connected pieces of an injective curve into lower bounds for its geometric
length.

The proof uses the distance from one endpoint as a real-valued Lipschitz function. Its image is
preconnected and contains the interval between zero and the distance to the other endpoint.

## Main results

* `IsPreconnected.edist_le_hausdorffMeasure` bounds each pairwise distance by Hausdorff length.
* `IsPreconnected.ediam_le_hausdorffMeasure` bounds the extended diameter by Hausdorff length.

The declarations and proof strategy follow
[Mathlib pull request #41839](https://github.com/leanprover-community/mathlib4/pull/41839),
available under Apache 2.0.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

/-- The distance between two points of a preconnected set is at most the set's
one-dimensional Hausdorff measure. -/
theorem _root_.IsPreconnected.edist_le_hausdorffMeasure {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : IsPreconnected s)
    {x y : X} (hx : x ∈ s) (hy : y ∈ s) : edist x y ≤ μH[1] s := by
  let f : X → ℝ := fun z ↦ (edist x z).toReal
  have hfinite (z : X) (hz : z ∈ s) : edist x z ≠ ∞ := hs.edist_ne_top hx hz
  have hf : LipschitzOnWith 1 f s := (lipschitzWith_toReal_edist x).lipschitzOnWith
  have hconn : IsPreconnected (f '' s) := hs.image f hf.continuousOn
  have hzero : (0 : ℝ) ∈ f '' s := ⟨x, hx, by simp [f]⟩
  have hdist : (edist x y).toReal ∈ f '' s := ⟨y, hy, rfl⟩
  have hIcc : Icc 0 (edist x y).toReal ⊆ f '' s := hconn.Icc_subset hzero hdist
  calc
    edist x y = ENNReal.ofReal (edist x y).toReal := (ENNReal.ofReal_toReal (hfinite y hy)).symm
    _ = volume (Icc 0 (edist x y).toReal) := by rw [Real.volume_Icc]; simp
    _ = μH[1] (Icc 0 (edist x y).toReal) := by rw [hausdorffMeasure_real]
    _ ≤ μH[1] (f '' s) := measure_mono hIcc
    _ ≤ μH[1] s := by simpa using hf.hausdorffMeasure_image_le zero_le_one

/-- The extended diameter of a preconnected set is at most its one-dimensional Hausdorff
measure. -/
theorem _root_.IsPreconnected.ediam_le_hausdorffMeasure {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {s : Set X} (hs : IsPreconnected s) :
    Metric.ediam s ≤ μH[1] s := by
  exact Metric.ediam_le fun _ hx _ hy ↦ hs.edist_le_hausdorffMeasure hx hy

end TauCeti
