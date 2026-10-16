/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Hausdorff measure and additive Haar measure

In dimension one, Euclidean-normalized Hausdorff measure agrees with raw Hausdorff measure. A set
of Hausdorff dimension below the dimension of its ambient finite-dimensional real normed space is
null for every normalization of additive Haar measure.
-/

public section

namespace MeasureTheory

namespace Measure

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- In dimension one the Euclidean normalization constant is `1`, so `μHE[1] = μH[1]`. -/
theorem euclideanHausdorffMeasure_one : (μHE[1] : Measure X) = μH[1] := by
  have hreal : (μHE[1] : Measure ℝ) = volume := by
    simpa using (InnerProductSpace.euclideanHausdorffMeasure_eq_volume (V := ℝ))
  have hscalar :
      addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 1))) μH[(1 : ℕ)] = 1 := by
    have h := congrArg (fun μ : Measure ℝ ↦ μ (Set.Icc 0 1)) hreal
    simpa [euclideanHausdorffMeasure_def, smul_apply, hausdorffMeasure_real,
      Real.volume_Icc] using h
  rw [euclideanHausdorffMeasure_def, hscalar, one_smul, Nat.cast_one]

end Measure

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
