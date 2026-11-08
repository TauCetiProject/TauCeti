/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.OuterMeasure.Basic

import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Proportions of sets and measurable hulls in outer measure

The proportion `μ (s ∩ t) / μ t` of a set `s` in a set `t` is at most one. This uses only
monotonicity, so it is stated for `OuterMeasureClass`, which covers both outer measures and
measures without requiring a measurable space.

The measurable hulls of sets of measure at most `(n + 1)⁻¹` have measure tending to zero.

## Main results

* `MeasureTheory.measure_inter_div_le_one`
* `MeasureTheory.tendsto_measure_toMeasurable_of_le_inv`
-/

public section

open Filter Set Topology
open scoped ENNReal

namespace MeasureTheory

variable {α F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] {μ : F}

/-- The proportion `μ (s ∩ t) / μ t` of a set `s` in a set `t` is at most one. -/
theorem measure_inter_div_le_one (s t : Set α) : μ (s ∩ t) / μ t ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_right)

/-- The measurable hulls of sets of measure at most `(n + 1)⁻¹` have measure tending to zero. -/
theorem tendsto_measure_toMeasurable_of_le_inv {α : Type*} {m : MeasurableSpace α}
    {μ : Measure α} {t : ℕ → Set α}
    (ht : ∀ n : ℕ, μ (t n) ≤ ((n : ℝ≥0∞) + 1)⁻¹) :
    Tendsto (fun n ↦ μ (toMeasurable μ (t n))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    refine (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)).congr fun n ↦ ?_
    simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hinv (fun _ ↦ zero_le)
    fun n ↦ ?_
  simpa only [measure_toMeasurable] using ht n

end MeasureTheory
