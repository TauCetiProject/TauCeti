/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Measures of superlevel sets of integrable functions

For `f ∈ Lᵖ` with `0 < p < ∞`, valued in a normed lattice such as `ℝ`, every superlevel set
`{ε < f}` with `ε > 0` has finite measure (`MeasureTheory.MemLp.measure_gt_lt_top`). This is
the non-quantitative Markov inequality `MeasureTheory.MemLp.meas_ge_lt_top'` stated for the
superlevel sets of `f` itself, as Mathlib's `MeasureTheory.Integrable.measure_gt_lt_top` does
for `p = 1`.

For an almost everywhere nonnegative integrable real function, Markov’s inequality bounds
the measure of a positive superlevel set by the integral divided by the threshold.
-/

public section

open scoped ENNReal

namespace MeasureTheory

/-- If `f ∈ Lᵖ` with `0 < p < ∞`, then for any `ε > 0` the set `{x | ε < f x}` has finite
measure. -/
theorem MemLp.measure_gt_lt_top {α β : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞}
    [NormedAddCommGroup β] [Lattice β] [HasSolidNorm β] [AddLeftMono β] {f : α → β}
    (hf : MemLp f p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) {ε : β} (hε : 0 < ε) :
    μ {x | ε < f x} < ∞ :=
  lt_of_le_of_lt (measure_mono fun x (hx : ε < f x) ↦ ENNReal.coe_le_coe.2 <|
      norm_le_norm_of_abs_le_abs <| (abs_of_nonneg hε.le).symm ▸ hx.le.trans (le_abs_self (f x)))
    (hf.meas_ge_lt_top' hp_ne_zero hp_ne_top (ε := ‖ε‖₊) (by simpa using hε.ne'))

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
