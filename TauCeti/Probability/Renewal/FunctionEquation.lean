/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Renewal.Equation

/-!
# The renewal equation for the mean count

When the renewal measure `U` is locally finite, the real-valued renewal function
`t ↦ (m t).toReal` solves the renewal equation with forcing `t ↦ F.real [0, t]`.
This file identifies that real-valued function with the convolution of the forcing and `U`,
and derives its renewal equation. By
`TauCeti.Probability.eq_renewalConv_renewalMeasure`, it is then the only measurable,
locally bounded real-valued solution.

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

/-- The mean renewal count solves the renewal equation with forcing `t ↦ F [0, t]`.
The atom at zero is retained in the convolution. -/
theorem renewalFunction_toReal_eq_add_renewalConv (μ : Measure ℝ≥0) [SFinite μ]
    [IsLocallyFiniteMeasure μ.renewalMeasure] (t : ℝ≥0) :
    (μ.renewalFunction t).toReal = μ.real (Iic t) +
      renewalConv (fun u ↦ (μ.renewalFunction u).toReal) μ t := by
  have := isLocallyFiniteMeasure_of_renewalMeasure μ
  have hmeas : Measurable (fun u ↦ μ.real (Iic u)) := by
    rw [← renewalConv_const_one]
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
This identity needs only local finiteness of the renewal measure and `F.real {0} ≠ 1`,
not probability normalization. -/
@[simp]
theorem renewalFunction_toReal_zero (μ : Measure ℝ≥0) [SFinite μ]
    [IsLocallyFiniteMeasure μ.renewalMeasure] (hμ : μ.real {0} ≠ 1) :
    (μ.renewalFunction 0).toReal = μ.real {0} / (1 - μ.real {0}) := by
  have heq : (fun u ↦ (μ.renewalFunction u).toReal) =
      (fun u ↦ μ.real (Iic u)) + renewalConv (fun u ↦ (μ.renewalFunction u).toReal) μ := by
    funext t
    exact renewalFunction_toReal_eq_add_renewalConv μ t
  -- Specialize the bottom-interval lemma to zero before rewriting under the measure.
  simpa only [show Iic (0 : ℝ≥0) = {0} from Iic_bot] using
    apply_zero_of_eq_add_renewalConv heq hμ

/-- The initial mean count for a probability increment law with `F {0} < 1`. -/
theorem renewalFunction_toReal_zero_of_isProbabilityMeasure (μ : Measure ℝ≥0)
    [IsProbabilityMeasure μ] (hμ : μ {0} < 1) :
    (μ.renewalFunction 0).toReal = μ.real {0} / (1 - μ.real {0}) := by
  let := isLocallyFiniteMeasure_renewalMeasure μ hμ
  have hlt : μ.real {0} < 1 := by
    simpa only [measureReal_def, ENNReal.toReal_one] using
      (ENNReal.toReal_lt_toReal (measure_ne_top μ _) ENNReal.one_ne_top).2 hμ
  exact renewalFunction_toReal_zero μ hlt.ne

end MeasureTheory.Measure
