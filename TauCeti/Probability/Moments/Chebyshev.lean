/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.MeasureTheory.Integral.Bochner.Markov

/-!
# Chebyshev's inequality for the second moment

For any measure `μ` and any function `Y` with values in a type with a norm, whose squared norm
is integrable, the set where `‖Y‖` is at least `c > 0` has measure at most `(∫ ‖Y‖²) / c²`. This is
Markov's inequality applied to `‖Y‖²`. Unlike `ProbabilityTheory.meas_ge_le_variance_div_sq`,
`Y` is not centered at its mean, so the bound applies directly to a deviation such as the error
of an estimator.

## Main statements

* `TauCeti.meas_ge_le_integral_norm_pow_div_pow`: Markov’s inequality for natural powers
  of the norm.
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

/-- Markov's inequality for a natural power of the norm at a positive threshold. For an arbitrary
`Norm` instance, assume the power is nonnegative almost everywhere. -/
theorem meas_ge_le_integral_norm_pow_div_pow [Norm E] {Y : Ω → E} (k : ℕ)
    (hY : Integrable (fun ω ↦ ‖Y ω‖ ^ k) μ) (hn : ∀ᵐ ω ∂μ, 0 ≤ ‖Y ω‖ ^ k)
    {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ ‖Y ω‖} ≤ ENNReal.ofReal ((∫ ω, ‖Y ω‖ ^ k ∂μ) / c ^ k) := by
  have hsub : {ω | c ≤ ‖Y ω‖} ⊆ {ω | c ^ k ≤ ‖Y ω‖ ^ k} :=
    fun _ hω ↦ pow_le_pow_left₀ hc.le hω k
  exact (measure_mono hsub).trans (hY.measure_ge_le_ofReal_integral_div hn (pow_pos hc k))

/-- **Chebyshev's inequality for the second moment.** For any measure, if `‖Y‖²` is integrable
and `0 < c`, the set where `‖Y‖` is at least `c` has measure at most `(∫ ‖Y‖²) / c²`. Unlike
`ProbabilityTheory.meas_ge_le_variance_div_sq`, `Y` is not centered at its mean. -/
theorem meas_ge_le_integral_norm_sq_div_sq [Norm E] {Y : Ω → E}
    (hY : Integrable (fun ω ↦ ‖Y ω‖ ^ 2) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ ‖Y ω‖} ≤ ENNReal.ofReal ((∫ ω, ‖Y ω‖ ^ 2 ∂μ) / c ^ 2) :=
  meas_ge_le_integral_norm_pow_div_pow 2 hY (.of_forall fun _ ↦ sq_nonneg _) hc

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
