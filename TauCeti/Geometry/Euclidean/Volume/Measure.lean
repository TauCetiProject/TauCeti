/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure

/-!
# The one-dimensional Euclidean Hausdorff measure

Mathlib's Euclidean Hausdorff measure `μHE[d]` is the raw Hausdorff measure `μH[d]` rescaled by
the constant that makes it agree with Lebesgue measure on `d`-dimensional Euclidean space. In
dimension one this constant is `1`, because `μH[1]` already agrees with Lebesgue measure on `ℝ`.
Hence `μHE[1] = μH[1]` on every extended metric space, so length statements may be proved with
either normalization.
-/

public section

open Set

namespace MeasureTheory.Measure

/-- The one-dimensional Euclidean Hausdorff measure is the raw one-dimensional Hausdorff measure,
on every extended metric space. -/
theorem euclideanHausdorffMeasure_one {X : Type*} [EMetricSpace X] [MeasurableSpace X]
    [BorelSpace X] : (μHE[1] : Measure X) = μH[1] := by
  have hℝ : (μHE[1] : Measure ℝ) = μH[1] := by
    rw [hausdorffMeasure_real, ← InnerProductSpace.euclideanHausdorffMeasure_eq_volume,
      Module.finrank_self]
  have hreal : (μH[((1 : ℕ) : ℝ)] : Measure ℝ) = volume := by
    rw [Nat.cast_one, hausdorffMeasure_real]
  have hc : addHaarScalarFactor (volume : Measure (EuclideanSpace ℝ (Fin 1)))
      μH[((1 : ℕ) : ℝ)] = 1 := by
    have h := congr($hℝ (Icc (0 : ℝ) 1))
    rw [euclideanHausdorffMeasure_def, smul_apply, hreal, hausdorffMeasure_real] at h
    simpa using h
  rw [euclideanHausdorffMeasure_def, hc, one_smul, Nat.cast_one]

end MeasureTheory.Measure
