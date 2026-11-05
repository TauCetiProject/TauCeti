/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Equation

/-!
# The renewal equation for the mean count

The renewal function `m` is the unique measurable, locally bounded solution of the renewal
equation with forcing `t ↦ F [0, t]`. This file identifies its real-valued version with the
convolution of that forcing and the renewal measure, and derives the equation
`m = F [0, ·] + m ∗ F`. The general uniqueness theorem is
`TauCeti.Probability.eq_renewalConv_renewalMeasure`.

All convolution intervals include both endpoints. Consequently, when `F` has an atom at zero,
the initial mean count is `F {0} / (1 - F {0})`, rather than zero. The nondegeneracy assumption
`F {0} < 1` ensures that the extended mean count is finite before it is converted to a real
number; no finite-mean assumption on the increments is needed.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II, 2nd
  edition, Wiley, 1971, Chapter XI, §1.
-/

public section

noncomputable section

open MeasureTheory Set
open TauCeti.Probability
open scoped ENNReal NNReal

namespace MeasureTheory.Measure

/-- The renewal function is the convolution of the increment distribution function with the
renewal measure. This holds whenever the renewal measure is locally finite, without probability
normalization of the increment measure. -/
theorem renewalConv_measureReal_Iic_renewalMeasure (μ : Measure ℝ≥0) [SFinite μ]
    [IsLocallyFiniteMeasure μ.renewalMeasure] (t : ℝ≥0) :
    renewalConv (fun u ↦ μ.real (Iic u)) μ.renewalMeasure t = (μ.renewalFunction t).toReal := by
  have := isLocallyFiniteMeasure_of_renewalMeasure μ
  have hcdf : (fun u ↦ μ.real (Iic u)) = renewalConv (fun _ ↦ 1) μ := by
    ext u
    simp
  rw [hcdf, renewalConv_renewalConv measurable_const (C := 1) (by simp)
    measure_Iic_lt_top.ne measure_Iic_lt_top.ne, renewalConv_const, mul_one,
    measureReal_def, renewalFunction_def]

/-- The mean renewal count solves the renewal equation with forcing `t ↦ F [0, t]`.
The atom at zero is retained in the convolution. -/
theorem renewalFunction_toReal_eq_add_renewalConv (μ : Measure ℝ≥0) [SFinite μ]
    [IsLocallyFiniteMeasure μ.renewalMeasure] (t : ℝ≥0) :
    (μ.renewalFunction t).toReal = μ.real (Iic t) +
      renewalConv (fun u ↦ (μ.renewalFunction u).toReal) μ t := by
  have := isLocallyFiniteMeasure_of_renewalMeasure μ
  have hcdf : (fun u ↦ μ.real (Iic u)) = renewalConv (fun _ ↦ 1) μ := by
    ext u
    simp
  have hmeas : Measurable (fun u ↦ μ.real (Iic u)) := by
    rw [hcdf]
    exact measurable_renewalConv measurable_const μ
  have hbound : ∀ s ≤ t, |μ.real (Iic s)| ≤ μ.real (Iic t) := fun s hs ↦ by
    rw [abs_of_nonneg measureReal_nonneg]
    exact measureReal_mono (Iic_subset_Iic.mpr hs) measure_Iic_lt_top.ne
  have heq := renewalConv_renewalMeasure_eq_add (μ := μ) hmeas hbound
  have hid : renewalConv (fun u ↦ μ.real (Iic u)) μ.renewalMeasure =
      fun u ↦ (μ.renewalFunction u).toReal :=
    funext (renewalConv_measureReal_Iic_renewalMeasure μ)
  rwa [hid] at heq

/-- At time zero the expected number of genuine arrivals is `F {0} / (1 - F {0})`.
In particular, an atom at zero yields a nonzero initial renewal function. -/
@[simp]
theorem renewalFunction_toReal_zero (μ : Measure ℝ≥0) [IsProbabilityMeasure μ]
    (hμ : μ {0} < 1) :
    (μ.renewalFunction 0).toReal = μ.real {0} / (1 - μ.real {0}) := by
  have hlt : μ.real {0} < 1 := by
    simpa only [measureReal_def, ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.one_ne_top).2 hμ
  let := isLocallyFiniteMeasure_renewalMeasure μ hμ
  have heq : (fun u ↦ (μ.renewalFunction u).toReal) =
      (fun u ↦ μ.real (Iic u)) + renewalConv (fun u ↦ (μ.renewalFunction u).toReal) μ := by
    funext t
    exact renewalFunction_toReal_eq_add_renewalConv μ t
  have hz : Iic (0 : ℝ≥0) = {0} := by ext s; simp
  simpa only [hz] using apply_zero_of_eq_add_renewalConv heq hlt.ne

end MeasureTheory.Measure
