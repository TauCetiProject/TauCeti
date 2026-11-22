/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Additive Haar nullness from Hausdorff dimension

A set of Hausdorff dimension below the dimension of its ambient finite-dimensional real normed
space is null for every normalization of additive Haar measure.
-/

public section

open scoped ENNReal

namespace MeasureTheory.Measure

/-- A set of smaller Hausdorff dimension than its ambient real normed space is null for every
additive Haar measure. -/
theorem addHaar_eq_zero_of_dimH_lt_finrank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hs : dimH s < Module.finrank ℝ E) :
    μ s = 0 := by
  -- the hypothesis forces `finrank ℝ E > 0`, so `E` is finite-dimensional
  have : FiniteDimensional ℝ E :=
    Module.finite_of_finrank_pos (Nat.cast_pos.mp (zero_le.trans_lt hs))
  have hμ : μ ≪ μH[(Module.finrank ℝ E : ℝ)] := absolutelyContinuous_isAddHaarMeasure μ _
  exact measure_zero_of_dimH_lt (d := (Module.finrank ℝ E : NNReal)) hμ (mod_cast hs)

/-- A set `s` satisfying `dimH s + 1 ≤ Module.finrank ℝ E` is null for every additive Haar measure
on `E`. -/
theorem addHaar_eq_zero_of_dimH_add_one_le_finrank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E}
    (hs : dimH s + 1 ≤ Module.finrank ℝ E) : μ s = 0 := by
  have hs_top : dimH s ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top _) (le_self_add.trans hs)
  exact μ.addHaar_eq_zero_of_dimH_lt_finrank
    ((ENNReal.lt_add_right hs_top one_ne_zero).trans_le hs)

/-- On a nontrivial finite-dimensional real normed space `E`, a set of Hausdorff dimension at most
`Module.finrank ℝ E - 1` is null for every additive Haar measure on `E`. -/
theorem addHaar_eq_zero_of_dimH_le_finrank_sub_one {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Nontrivial E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E}
    (hs : dimH s ≤ ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞)) : μ s = 0 := by
  refine μ.addHaar_eq_zero_of_dimH_add_one_le_finrank ?_
  have hcast : ((Module.finrank ℝ E - 1 : ℕ) : ℝ≥0∞) + 1 = Module.finrank ℝ E := by
    exact_mod_cast Nat.sub_add_cancel Module.finrank_pos
  exact (add_le_add_left hs 1).trans_eq hcast

end MeasureTheory.Measure
