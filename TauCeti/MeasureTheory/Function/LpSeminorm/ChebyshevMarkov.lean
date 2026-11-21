/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Markov tail bounds for `Lᵖ` functions and section integrals

For `f ∈ Lᵖ` with `0 < p < ∞`, valued in a normed lattice such as `ℝ`, every superlevel set
`{ε < f}` with `ε > 0` has finite measure (`MeasureTheory.MemLp.measure_gt_lt_top`). This is
the non-quantitative Markov inequality `MeasureTheory.MemLp.meas_ge_lt_top'` stated for the
superlevel sets of `f` itself, as Mathlib's `MeasureTheory.Integrable.measure_gt_lt_top` does
for `p = 1`.

For a family `g k : α × β → E` converging to `0` in `Lⁿ(μ.prod ν)` (`n ≠ 0`), the slice lower
integrals `∫⁻ x, ‖g k (x, y)‖ₑ ^ n ∂μ` converge to `0` in `ν`-measure
(`MeasureTheory.tendsto_measure_le_lintegral_enorm_pow_of_tendsto_eLpNorm`).
-/

public section

open Filter
open scoped ENNReal Topology

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

/-- If `eLpNorm (g k) n (μ.prod ν) → 0` for `n ≠ 0` along a filter `l`, then the slice energies
`∫⁻ x, ‖g k (x, y)‖ₑ ^ n ∂μ` converge to `0` in `ν`-measure. -/
theorem tendsto_measure_le_lintegral_enorm_pow_of_tendsto_eLpNorm
    {α β ι E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    [TopologicalSpace E] [ContinuousENorm E]
    {l : Filter ι} {n : ℕ} (hn : n ≠ 0) {g : ι → α × β → E}
    (hg : ∀ k, AEStronglyMeasurable (g k) (μ.prod ν))
    (hlim : Tendsto (fun k ↦ eLpNorm (g k) n (μ.prod ν)) l (𝓝 0))
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    Tendsto (fun k ↦ ν {y | ε ≤ ∫⁻ x, ‖g k (x, y)‖ₑ ^ n ∂μ}) l (𝓝 0) := by
  have hm (k : ι) : AEMeasurable (fun p : α × β ↦ ‖g k p‖ₑ ^ n) (μ.prod ν) :=
    (hg k).eNorm.pow_const n
  have hint (k : ι) : ∫⁻ y, ∫⁻ x, ‖g k (x, y)‖ₑ ^ n ∂μ ∂ν = eLpNorm (g k) n (μ.prod ν) ^ n := by
    rw [← lintegral_prod_symm _ (hm k),
      TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow hn (hg k)]
  have hpow : Tendsto (fun k ↦ eLpNorm (g k) n (μ.prod ν) ^ n) l (𝓝 0) := by
    simpa only [Function.comp_def, zero_pow hn] using
      (ENNReal.continuous_pow n).continuousAt.tendsto.comp hlim
  by_cases htop : ε = ∞
  · subst htop
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpow.eventually (gt_mem_nhds zero_lt_one)] with k hk
    have hae := ae_lt_top' (hm k).lintegral_prod_left'
      ((hint k).trans_lt (hk.trans ENNReal.one_lt_top)).ne
    simpa only [not_lt, top_le_iff] using (ae_iff.mp hae).symm
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [mul_zero] using
        ENNReal.Tendsto.const_mul hpow (Or.inr (ENNReal.inv_ne_top.mpr hε.ne')))
      (fun _ ↦ bot_le) fun k ↦ ?_
    calc ν {y | ε ≤ ∫⁻ x, ‖g k (x, y)‖ₑ ^ n ∂μ}
      _ = ε⁻¹ * (ε * ν {y | ε ≤ ∫⁻ x, ‖g k (x, y)‖ₑ ^ n ∂μ}) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hε.ne' htop, one_mul]
      _ ≤ ε⁻¹ * eLpNorm (g k) n (μ.prod ν) ^ n := mul_le_mul_right
          ((mul_meas_ge_le_lintegral₀ (hm k).lintegral_prod_left' ε).trans_eq (hint k)) _

end MeasureTheory
