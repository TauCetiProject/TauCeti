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

namespace MeasureTheory

/-- A set of smaller Hausdorff dimension than its ambient real normed space is null for every
additive Haar measure. -/
theorem addHaar_eq_zero_of_dimH_lt_finrank {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] {s : Set E} (hs : dimH s < Module.finrank ℝ E) :
    μ s = 0 := by
  have hμ : μ ≪ μH[(Module.finrank ℝ E : ℝ)] :=
    Measure.absolutelyContinuous_isAddHaarMeasure μ _
  apply measure_zero_of_dimH_lt (d := (Module.finrank ℝ E : NNReal)) hμ
  simpa only [ENNReal.coe_natCast] using hs

end MeasureTheory
