/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Chebyshev's inequality for the second moment

For any measure `μ` and any function `Y` with values in a type with a norm, whose squared norm
is integrable, the set where `‖Y‖` is at least `c > 0` has measure at most `(∫ ‖Y‖²) / c²`. This is
Markov's inequality applied to `‖Y‖²`. Unlike `ProbabilityTheory.meas_ge_le_variance_div_sq`,
`Y` is not centered at its mean, so the bound applies directly to a deviation such as the error
of an estimator.

## Main statements

* `MeasureTheory.Integrable.measure_ge_le_ofReal_integral_div` gives Markov's inequality
  for the extended measure of a superlevel set of a nonnegative integrable real function.
* `TauCeti.meas_ge_le_integral_norm_sq_div_sq`: Chebyshev's inequality for the second moment,
  `μ {c ≤ ‖Y‖} ≤ (∫ ‖Y‖²) / c²`, for any measure and without centering.
* `TauCeti.meas_gt_le_div_sq_of_integral_sq_le`: the uncentered Chebyshev inequality
  `μ {η < Y} ≤ v / η²` for a real `Y` with `∫ Y² ≤ v`.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §1.2: Chebyshev's inequality.
-/

public section

open MeasureTheory

namespace TauCeti

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- Markov's inequality for the extended measure of a positive superlevel set of an
integrable, almost everywhere nonnegative real function. -/
theorem _root_.MeasureTheory.Integrable.measure_ge_le_ofReal_integral_div
    {f : Ω → ℝ} (hf : Integrable f μ) (hnonneg : 0 ≤ᵐ[μ] f) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂μ) / c) := by
  have hsub : {ω | c ≤ f ω} ⊆ {ω | ENNReal.ofReal c ≤ ENNReal.ofReal (f ω)} :=
    fun _ hω ↦ ENNReal.ofReal_le_ofReal hω
  refine (measure_mono hsub).trans ?_
  refine (meas_ge_le_lintegral_div hf.aemeasurable.ennreal_ofReal
    (ENNReal.ofReal_pos.2 hc).ne' ENNReal.ofReal_ne_top).trans_eq ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hf hnonneg, ENNReal.ofReal_div_of_pos hc]

/-- **Chebyshev's inequality for the second moment.** For any measure, if `‖Y‖²` is integrable
and `0 < c`, the set where `‖Y‖` is at least `c` has measure at most `(∫ ‖Y‖²) / c²`. Unlike
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `Y` is not centered at its mean. -/
theorem meas_ge_le_integral_norm_sq_div_sq [Norm E] {Y : Ω → E}
    (hY : Integrable (fun ω ↦ ‖Y ω‖ ^ 2) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ ‖Y ω‖} ≤ ENNReal.ofReal ((∫ ω, ‖Y ω‖ ^ 2 ∂μ) / c ^ 2) := by
  have hsub : {ω | c ≤ ‖Y ω‖} ⊆ {ω | c ^ 2 ≤ ‖Y ω‖ ^ 2} :=
    fun _ hω ↦ pow_le_pow_left₀ hc.le hω 2
  refine (measure_mono hsub).trans ?_
  exact hY.measure_ge_le_ofReal_integral_div (.of_forall fun _ ↦ sq_nonneg _) (sq_pos_of_pos hc)

/-- **The uncentered Chebyshev inequality.** If `Y²` is integrable with `∫ Y² ≤ v` and `0 < η`,
then the set where `Y` exceeds `η` has measure at most `v / η²`. -/
theorem meas_gt_le_div_sq_of_integral_sq_le {Y : Ω → ℝ} (hY : Integrable (fun ω ↦ Y ω ^ 2) μ)
    {v η : ℝ} (hv : ∫ ω, Y ω ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    μ {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) := by
  have hY' : Integrable (fun ω ↦ ‖Y ω‖ ^ 2) μ := by simpa only [Real.norm_eq_abs, sq_abs] using hY
  calc μ {ω | η < Y ω}
      ≤ μ {ω | η ≤ ‖Y ω‖} :=
        measure_mono fun ω (hω : η < Y ω) ↦ hω.le.trans (Real.le_norm_self (Y ω))
    _ ≤ ENNReal.ofReal ((∫ ω, ‖Y ω‖ ^ 2 ∂μ) / η ^ 2) := meas_ge_le_integral_norm_sq_div_sq hY' hη
    _ ≤ ENNReal.ofReal (v / η ^ 2) := by
        simp only [Real.norm_eq_abs, sq_abs]
        gcongr

end TauCeti
