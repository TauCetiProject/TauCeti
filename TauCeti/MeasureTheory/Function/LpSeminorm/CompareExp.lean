/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# `Lᵖ` convergence gives `L¹` convergence on a finite measure space

On a finite measure space, Mathlib's exponent comparison
`eLpNorm_le_eLpNorm_mul_rpow_measure_univ` bounds the `L¹` seminorm by the `Lᵖ` seminorm (for
`1 ≤ p`) times a finite constant. This file packages that comparison as a convergence statement
both for the `L¹` seminorm and for the Bochner integral `∫ ‖f i‖ ∂μ`, the form in which `L¹`
convergence of a difference `f i = W i - a` is usually consumed.

## Main declarations

* `TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm`: convergence to zero in `Lᵖ`
  for `1 ≤ p` implies convergence to zero in `L¹`.
* `TauCeti.MeasureTheory.tendsto_integral_norm_of_tendsto_eLpNorm`: if `eLpNorm (f i) p μ → 0`
  for some `1 ≤ p`, then `∫ ‖f i‖ ∂μ → 0`.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- On a finite measure space, convergence to zero in `Lᵖ` for `1 ≤ p` implies convergence
to zero in `L¹`. No measurability hypothesis or finiteness assumption on `p` is needed. -/
theorem tendsto_eLpNorm_one_of_tendsto_eLpNorm {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0)) :
    Tendsto (fun i => eLpNorm (f i) 1 μ) l (𝓝 0) := by
  have hexp : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal := by
    rcases eq_or_ne p ∞ with rfl | hp_top
    · simp
    rw [ENNReal.toReal_one, sub_nonneg]
    gcongr
    simpa using ENNReal.toReal_mono hp_top hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
    fun _ => eLpNorm_le_eLpNorm_mul_rpow_measure_univ_of_pos hp one_pos
  simpa using ENNReal.Tendsto.mul_const h
    (.inr (ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ Set.univ)))

/-- **`Lᵖ` convergence implies `L¹` convergence on a finite measure space.** If `1 ≤ p` and a
family `f` tends to `0` in `Lᵖ` along a filter `l`, then `∫ ‖f i‖` tends to `0` along `l`.
No measurability hypothesis is needed: `eLpNorm (f i) p μ` is finite eventually along `l`, which
forces `f i` to be a.e. strongly measurable. -/
theorem tendsto_integral_norm_of_tendsto_eLpNorm {ι E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} {μ : Measure Ω} [IsFiniteMeasure μ] {f : ι → Ω → E} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (h : Tendsto (fun i => eLpNorm (f i) p μ) l (𝓝 0)) :
    Tendsto (fun i => ∫ ω, ‖f i ω‖ ∂μ) l (𝓝 0) := by
  have hL1 := tendsto_eLpNorm_one_of_tendsto_eLpNorm hp h
  have hreal : Tendsto (fun i => (eLpNorm (f i) 1 μ).toReal) l (𝓝 0) := by
    simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hL1
  refine hreal.congr' ?_
  filter_upwards [h.eventually_lt_const ENNReal.zero_lt_top] with i hi
  have hf := aestronglyMeasurable_of_eLpNorm_ne_top hi.ne
  rw [eLpNorm_one_eq_lintegral_enorm hf, integral_norm_eq_lintegral_enorm hf]

end MeasureTheory

end TauCeti
