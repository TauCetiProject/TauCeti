/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Markov's inequality for the Bochner integral

For an almost everywhere nonnegative integrable real function, Markov's inequality bounds the
extended measure of a positive superlevel set by the Bochner integral divided by the threshold.
Unlike Mathlib's `MeasureTheory.mul_meas_ge_le_integral_of_nonneg`, the bound is stated in
`ℝ≥0∞` and holds for an arbitrary measure.

## Main results

* `MeasureTheory.Integrable.measure_ge_le_ofReal_integral_div`:
  `μ {c ≤ f} ≤ ENNReal.ofReal ((∫ f) / c)` for `0 < c`.
-/

public section

namespace MeasureTheory

/-- Markov's inequality for the extended measure of a positive superlevel set of an
integrable, almost everywhere nonnegative real function. -/
theorem Integrable.measure_ge_le_ofReal_integral_div
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {f : Ω → ℝ}
    (hf : Integrable f μ) (hnonneg : 0 ≤ᵐ[μ] f) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂μ) / c) := by
  have hsub : {ω | c ≤ f ω} ⊆ {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (f ω)} :=
    fun _ hω ↦ ENNReal.ofReal_le_ofReal hω
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div hf.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top).trans_eq ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnonneg, ENNReal.ofReal_div_of_pos hc]

end MeasureTheory
