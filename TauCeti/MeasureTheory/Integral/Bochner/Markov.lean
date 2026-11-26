/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Markov's inequality for a natural power

For any measure and any real function `Y` whose `k`-th power is integrable and almost everywhere
nonnegative, the set where `Y` is at least `c > 0` has extended measure at most
`(∫ Y ^ k) / c ^ k`. This is Mathlib's `MeasureTheory.Integrable.measure_le_integral` applied to
`Y ^ k / c ^ k`. Taking `Y = ‖Z‖` bounds the set where the norm of a function `Z` is at least `c`
by its `k`-th absolute moment, and so also the set where it exceeds `c`.

## Main results

* `TauCeti.meas_ge_le_integral_pow_div_pow`: `μ {c ≤ Y} ≤ (∫ Y ^ k) / c ^ k` for `0 < c`.
* `TauCeti.meas_norm_gt_le_integral_norm_pow_div_pow`: `μ {c < ‖Z‖} ≤ (∫ ‖Z‖ ^ k) / c ^ k` for
  `0 < c`.
-/

public section

open MeasureTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Markov's inequality for a natural power.** For any measure, if `Y ^ k` is integrable and
almost everywhere nonnegative and `0 < c`, the set where `Y` is at least `c` has measure at most
`(∫ Y ^ k) / c ^ k`. Taking `Y = ‖Z‖` gives the bound for the set where `‖Z‖` is at least `c`. -/
theorem meas_ge_le_integral_pow_div_pow {Y : Ω → ℝ} (k : ℕ) (hY : Integrable (fun ω ↦ Y ω ^ k) μ)
    (hn : ∀ᵐ ω ∂μ, 0 ≤ Y ω ^ k) {c : ℝ} (hc : 0 < c) :
    μ {ω | c ≤ Y ω} ≤ ENNReal.ofReal ((∫ ω, Y ω ^ k ∂μ) / c ^ k) := by
  have hck : 0 < c ^ k := pow_pos hc k
  rw [← integral_div]
  exact (hY.div_const _).measure_le_integral (hn.mono fun _ h ↦ div_nonneg h hck.le)
    fun _ hω ↦ (one_le_div hck).2 (pow_le_pow_left₀ hc.le hω k)

/-- **Markov's inequality for the norm.** For any measure, if `‖Z‖ ^ k` is integrable and
`0 < c`, the set where `‖Z‖` exceeds `c` has measure at most `(∫ ‖Z‖ ^ k) / c ^ k`. -/
theorem meas_norm_gt_le_integral_norm_pow_div_pow {E : Type*} [SeminormedAddGroup E] {Z : Ω → E}
    (k : ℕ) (hZ : Integrable (fun ω ↦ ‖Z ω‖ ^ k) μ) {c : ℝ} (hc : 0 < c) :
    μ {ω | c < ‖Z ω‖} ≤ ENNReal.ofReal ((∫ ω, ‖Z ω‖ ^ k ∂μ) / c ^ k) :=
  (measure_mono (Set.ofPred_subset_ofPred.2 fun _ ↦ le_of_lt)).trans
    (meas_ge_le_integral_pow_div_pow k hZ (.of_forall fun _ ↦ by positivity) hc)

end TauCeti
