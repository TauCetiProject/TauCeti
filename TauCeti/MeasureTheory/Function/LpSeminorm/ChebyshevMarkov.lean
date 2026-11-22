/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Markov and Chebyshev point-selection inequalities in `Lᵖ`

For `f ∈ Lᵖ` with `0 < p < ∞`, valued in a normed lattice such as `ℝ`, every superlevel set
`{ε < f}` with `ε > 0` has finite measure (`MeasureTheory.MemLp.measure_gt_lt_top`). This is
the non-quantitative Markov inequality `MeasureTheory.MemLp.meas_ge_lt_top'` stated for the
superlevel sets of `f` itself, as Mathlib's `MeasureTheory.Integrable.measure_gt_lt_top` does
for `p = 1`.

On a nonzero finite measure space, every `f ∈ Lᵖ` with `0 < p < ∞` satisfies
`(μ univ) ^ (1 / p) ‖f x‖ₑ ≤ ‖f‖_p` on a set of positive measure
(`MeasureTheory.MemLp.frequently_measure_univ_rpow_mul_enorm_le_eLpNorm`), and in particular at
some point of any set of positive finite measure
(`MeasureTheory.MemLp.exists_mem_measure_rpow_mul_enorm_le_eLpNorm`).
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

section PointSelection

variable {α ε : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε] [ContinuousENorm ε]

/-- **Chebyshev point selection in `Lᵖ`.** On a nonzero finite measure space, a function in `Lᵖ` for
`0 < p < ∞` satisfies `(μ Set.univ) ^ (1 / p) ‖f x‖ₑ ≤ ‖f‖_{Lᵖ(μ)}` on a set of positive measure
(in particular, at some point). -/
theorem MemLp.frequently_measure_univ_rpow_mul_enorm_le_eLpNorm {f : α → ε} {p : ℝ≥0∞}
    (hf : MemLp f p μ) (hp0 : p ≠ 0) (hp : p ≠ ∞) (hμ0 : μ ≠ 0) (hμ : μ Set.univ ≠ ∞) :
    ∃ᵐ x ∂μ, (μ Set.univ) ^ p.toReal⁻¹ * ‖f x‖ₑ ≤ eLpNorm f p μ := by
  by_contra h
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hμ0' : μ Set.univ ≠ 0 := mt Measure.measure_univ_eq_zero.1 hμ0
  have hlt : ∀ᵐ x ∂μ, eLpNorm f p μ ^ p.toReal / μ Set.univ < ‖f x‖ₑ ^ p.toReal := by
    filter_upwards [Filter.not_frequently.1 h] with x hx
    have hpow := ENNReal.rpow_lt_rpow (not_le.1 hx) hpr
    rw [ENNReal.mul_rpow_of_nonneg _ _ hpr.le, ← ENNReal.rpow_mul, inv_mul_cancel₀ hpr.ne',
      ENNReal.rpow_one] at hpow
    exact (ENNReal.div_lt_iff (Or.inl hμ0') (Or.inl hμ)).2 (by rwa [mul_comm])
  have hfin : ∫⁻ _x, eLpNorm f p μ ^ p.toReal / μ Set.univ ∂μ ≠ ∞ := by
    rw [lintegral_const, ENNReal.div_mul_cancel hμ0' hμ]
    exact ENNReal.rpow_ne_top_of_nonneg hpr.le hf.eLpNorm_ne_top
  have hstrict := lintegral_strict_mono hμ0 (hf.aestronglyMeasurable.eNorm.pow_const p.toReal)
    hfin hlt
  rw [lintegral_const, ENNReal.div_mul_cancel hμ0' hμ,
    lintegral_rpow_enorm_eq_eLpNorm_rpow hp0 hp hf.aestronglyMeasurable] at hstrict
  exact lt_irrefl _ hstrict

/-- **Chebyshev point selection on a set in `Lᵖ`.** On a set `s` of positive finite measure, a
function in `Lᵖ(μ.restrict s)` for `0 < p < ∞` satisfies `(μ s) ^ (1 / p) ‖f x‖ₑ ≤ ‖f‖_{Lᵖ(s)}`
at some point `x ∈ s`. -/
theorem MemLp.exists_mem_measure_rpow_mul_enorm_le_eLpNorm {f : α → ε} {p : ℝ≥0∞} {s : Set α}
    (hf : MemLp f p (μ.restrict s)) (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hμ0 : μ s ≠ 0) (hμ : μ s ≠ ∞) :
    ∃ x ∈ s, (μ s) ^ p.toReal⁻¹ * ‖f x‖ₑ ≤ eLpNorm f p (μ.restrict s) := by
  have hfreq := hf.frequently_measure_univ_rpow_mul_enorm_le_eLpNorm hp0 hp
    (mt (congrArg (· Set.univ)) (by simpa using hμ0)) (by simpa using hμ)
  rw [Measure.restrict_apply_univ] at hfreq
  have hne : μ ({x | (μ s) ^ p.toReal⁻¹ * ‖f x‖ₑ ≤ eLpNorm f p (μ.restrict s)} ∩ s) ≠ 0 := by
    rw [← Measure.restrict_apply₀
      (nullMeasurableSet_le (hf.aestronglyMeasurable.eNorm.const_mul _) aemeasurable_const)]
    exact frequently_ae_iff.1 hfreq
  obtain ⟨x, hx, hxs⟩ := nonempty_of_measure_ne_zero hne
  exact ⟨x, hxs, hx⟩

end PointSelection

end MeasureTheory
