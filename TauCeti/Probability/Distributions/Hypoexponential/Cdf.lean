/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypoexponential.Support
public import TauCeti.Probability.Cdf

/-!
# Qualitative cdf of hypoexponential laws

For a nonempty family of positive rates, the hypoexponential cdf is continuous, vanishes on
`(-∞, 0]`, increases strictly on `[0, ∞)`, and stays below one at every finite point. These
properties follow from absolute continuity and the exact support `[0, ∞)`, so they hold for
arbitrary repeated rates. They make the quantile the unique positive root of the cdf.

## References

* S. M. Ross, *Introduction to Probability Models*, 12th ed., Academic Press (2019), Chapter 5.
-/

public section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι] {r : ι → ℝ} {x : ℝ}

/-- A nonempty hypoexponential cdf with positive rates is continuous. -/
theorem continuous_cdf_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    Continuous (cdf (hypoexponentialMeasure r)) := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  exact Measure.continuous_cdf_of_noAtoms _

/-- A nonempty hypoexponential cdf with positive rates increases strictly on `[0, ∞)`. -/
theorem strictMonoOn_cdf_hypoexponentialMeasure (hr : ∀ i, 0 < r i) :
    StrictMonoOn (cdf (hypoexponentialMeasure r)) (Ici 0) := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  exact Measure.strictMonoOn_cdf_of_subset_support _ ordConnected_Ici
    (support_hypoexponentialMeasure hr).symm.subset

/-- A nonempty hypoexponential cdf vanishes at and below zero. -/
@[simp]
theorem cdf_hypoexponentialMeasure_of_nonpos (hr : ∀ i, 0 < r i) (hx : x ≤ 0) :
    cdf (hypoexponentialMeasure r) x = 0 := by
  let _ := isProbabilityMeasure_hypoexponentialMeasure hr
  rw [cdf_eq_real, measureReal_def, measure_mono_null
    (fun y hy ↦ not_lt.2 ((mem_Iic.1 hy).trans hx)) (ae_iff.1 (ae_pos_hypoexponentialMeasure r)),
    ENNReal.toReal_zero]

/-- A nonempty hypoexponential cdf with positive rates is positive exactly above zero. -/
@[simp]
theorem cdf_hypoexponentialMeasure_pos_iff (hr : ∀ i, 0 < r i) :
    0 < cdf (hypoexponentialMeasure r) x ↔ 0 < x := by
  refine ⟨fun h ↦ not_le.1 fun hx ↦ ?_, fun hx ↦ ?_⟩
  · simp [cdf_hypoexponentialMeasure_of_nonpos hr hx] at h
  · rw [← cdf_hypoexponentialMeasure_of_nonpos hr le_rfl]
    exact strictMonoOn_cdf_hypoexponentialMeasure hr self_mem_Ici hx.le hx

/-- A nonempty hypoexponential cdf with positive rates is below one at every finite point. -/
theorem cdf_hypoexponentialMeasure_lt_one (hr : ∀ i, 0 < r i) (x : ℝ) :
    cdf (hypoexponentialMeasure r) x < 1 :=
  Measure.cdf_lt_one_of_strictMonoOn_Ici _ (strictMonoOn_cdf_hypoexponentialMeasure hr) x

end TauCeti.Probability
