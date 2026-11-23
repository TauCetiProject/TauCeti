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

For any measure `μ` and any real function `Y` whose square is integrable, the set where `Y` is at
least `c > 0` has measure at most `(∫ Y²) / c²`. This is Markov's inequality applied to `Y²`.
Taking `Y = ‖Z‖` bounds the set where the norm of a function `Z` is at least `c`. Unlike
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `Y` is not centered at its mean, so the bound
applies directly to a deviation such as the error of an estimator.

## Main statements

* `TauCeti.meas_ge_le_integral_sq_div_sq`: Chebyshev's inequality for the second moment,
  `μ {c ≤ Y} ≤ (∫ Y²) / c²`, for any measure and without centering.
* `TauCeti.meas_gt_le_div_sq_of_integral_sq_le`: the uncentered Chebyshev inequality
  `μ {η < Y} ≤ v / η²` for a real `Y` with `∫ Y² ≤ v`.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §1.2: Chebyshev's inequality.
-/

public section

open MeasureTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Chebyshev's inequality for the second moment.** For any measure, if `Y²` is integrable and
`0 < c`, the set where `Y` is at least `c` has measure at most `(∫ Y²) / c²`. Taking `Y = ‖Z‖`
gives the bound for the set where `‖Z‖` is at least `c`. Unlike
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `Y` is not centered at its mean. -/
theorem meas_ge_le_integral_sq_div_sq {Y : Ω → ℝ} (hY : Integrable (fun ω ↦ Y ω ^ 2) μ)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ Y ω} ≤ ENNReal.ofReal ((∫ ω, Y ω ^ 2 ∂μ) / c ^ 2) := by
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  calc μ {ω | c ≤ Y ω}
      ≤ μ {ω | ENNReal.ofReal (c ^ 2) ≤ ENNReal.ofReal (Y ω ^ 2)} :=
        measure_mono fun ω (hω : c ≤ Y ω) ↦
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hc.le hω 2)
    _ ≤ (∫⁻ ω, ENNReal.ofReal (Y ω ^ 2) ∂μ) / ENNReal.ofReal (c ^ 2) :=
        meas_ge_le_lintegral_div hY.aemeasurable.ennreal_ofReal
          (ENNReal.ofReal_pos.2 hc2).ne' ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((∫ ω, Y ω ^ 2 ∂μ) / c ^ 2) := by
        rw [← ofReal_integral_eq_lintegral_ofReal hY (.of_forall fun ω ↦ by positivity),
          ENNReal.ofReal_div_of_pos hc2]

/-- **The uncentered Chebyshev inequality.** If `Y²` is integrable with `∫ Y² ≤ v` and `0 < η`,
then the set where `Y` exceeds `η` has measure at most `v / η²`. -/
theorem meas_gt_le_div_sq_of_integral_sq_le {Y : Ω → ℝ} (hY : Integrable (fun ω ↦ Y ω ^ 2) μ)
    {v η : ℝ} (hv : ∫ ω, Y ω ^ 2 ∂μ ≤ v) (hη : 0 < η) :
    μ {ω | η < Y ω} ≤ ENNReal.ofReal (v / η ^ 2) :=
  calc μ {ω | η < Y ω}
      ≤ μ {ω | η ≤ Y ω} := measure_mono fun ω (hω : η < Y ω) ↦ hω.le
    _ ≤ ENNReal.ofReal ((∫ ω, Y ω ^ 2 ∂μ) / η ^ 2) := meas_ge_le_integral_sq_div_sq hY hη
    _ ≤ ENNReal.ofReal (v / η ^ 2) := by gcongr

end TauCeti
