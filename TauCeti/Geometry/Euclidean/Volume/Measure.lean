/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Euclidean.Volume.Measure
public import TauCeti.MeasureTheory.Measure.Hausdorff

/-!
# Comparing Euclidean and raw Hausdorff measures

Mathlib's Euclidean Hausdorff measure `μHE[d]` is the raw Hausdorff measure `μH[d]` rescaled by
the constant that makes it agree with Lebesgue measure on `d`-dimensional Euclidean space. This
constant is positive and finite, so the two normalizations have the same null sets and the same
sets of finite measure; statements of either kind may be proved with either normalization.
In dimension zero, Hausdorff measure is counting measure
(`TauCeti.hausdorffMeasure_zero_eq_count`). In dimension one the normalizing constant is `1`,
because `μH[1]` already agrees with Lebesgue measure on `ℝ`. Hence `μHE[1] = μH[1]` on every
extended metric space, so length statements may be proved with either normalization.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

section Comparison

variable {X : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- A set is null for the Euclidean Hausdorff measure `μHE[d]` if and only if it is null for the
raw Hausdorff measure `μH[d]`. -/
@[simp]
theorem euclideanHausdorffMeasure_eq_zero_iff {d : ℕ} {s : Set X} :
    μHE[d] s = 0 ↔ μH[d] s = 0 := by
  rw [euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def, smul_eq_mul, mul_eq_zero,
    ENNReal.coe_eq_zero,
    or_iff_right (addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d)]

/-- A set has finite Euclidean Hausdorff measure `μHE[d]` if and only if it has finite raw
Hausdorff measure `μH[d]`. -/
@[simp]
theorem euclideanHausdorffMeasure_lt_top_iff {d : ℕ} {s : Set X} :
    μHE[d] s < ∞ ↔ μH[d] s < ∞ := by
  rw [euclideanHausdorffMeasure_def, smul_apply, ENNReal.smul_def, smul_eq_mul]
  simp [lt_top_iff_ne_top, ENNReal.mul_eq_top, addHaarScalarFactor_volume_hausdorffMeasure_ne_zero]

end Comparison

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
