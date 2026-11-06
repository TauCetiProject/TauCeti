/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# The `Lᵖ` integral is bounded by the `p`-th power of the `Lᵖ` seminorm

For a finite exponent `p ≠ 0`, Mathlib's `MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral` identifies
`eLpNorm f p μ ^ p` with `∫⁻ ‖f‖ₑ ^ p ∂μ` for an almost everywhere strongly measurable `f`. Without
measurability the seminorm is `∞` by convention, so the inequality
`∫⁻ ‖f‖ₑ ^ p ∂μ ≤ eLpNorm f p μ ^ p` holds for every `f`
(`TauCeti.lintegral_rpow_enorm_le_rpow_eLpNorm`). This is the form in which a bound on the `Lᵖ`
seminorm is used to bound an integral, with no measurability side condition. In the same form,
Hölder's inequality bounds the integral of `‖f‖ₑ` over a set `s` by
`μ s ^ (1 - 1/p) * eLpNorm f p μ` for `1 ≤ p`
(`TauCeti.setLIntegral_enorm_le_measure_rpow_mul_eLpNorm`).

Consequently a function in `Lᵖ` for `p ≠ 0` is finite almost everywhere
(`MeasureTheory.MemLp.ae_enorm_lt_top`), including for `p = ∞`.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

variable {α ε : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε] [ContinuousENorm ε]

namespace TauCeti

/-- For `p ≠ 0`, the integral `∫⁻ ‖f‖ₑ ^ p ∂μ` is at most `eLpNorm f p μ ^ p`, whether or not `f` is
almost everywhere strongly measurable. -/
theorem lintegral_rpow_enorm_le_rpow_eLpNorm {p : ℝ≥0} (hp : p ≠ 0) (f : α → ε) :
    ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ ≤ eLpNorm f p μ ^ (p : ℝ) := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact (eLpNorm_nnreal_pow_eq_lintegral hp hf).ge
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.top_rpow_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hp))]
    exact le_top

/-- **Hölder's inequality on a set.** For `1 ≤ p`, the integral of `‖f‖ₑ` over `s` is at most
`μ s ^ (1 - 1/p) * eLpNorm f p μ`, whether or not `f` is almost everywhere strongly measurable. -/
theorem setLIntegral_enorm_le_measure_rpow_mul_eLpNorm {p : ℝ≥0} (hp : 1 ≤ p) (s : Set α)
    (f : α → ε) : ∫⁻ x in s, ‖f x‖ₑ ∂μ ≤ μ s ^ (1 - (p : ℝ)⁻¹) * eLpNorm f p μ := by
  have hle : eLpNorm f p (μ.restrict s) ≤ eLpNorm f p μ :=
    eLpNorm_mono_measure f Measure.restrict_le_self
  by_cases hf : AEStronglyMeasurable f (μ.restrict s)
  · have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ.restrict s) (p := 1)
      (q := (p : ℝ≥0∞)) (by exact_mod_cast hp) hf
    rw [eLpNorm_one_eq_lintegral_enorm hf] at h
    simp only [Measure.restrict_apply_univ, ENNReal.toReal_one, div_one, ENNReal.coe_toReal,
      one_div] at h
    rw [mul_comm]
    exact h.trans (by gcongr)
  · rw [eLpNorm_of_not_aestronglyMeasurable hf, top_le_iff] at hle
    rcases eq_or_ne (μ s) 0 with h0 | h0
    · simp [Measure.restrict_eq_zero.2 h0]
    · have hp' : (p : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp)
      rw [hle, ENNReal.mul_top (by simp [h0, hp'])]
      exact le_top

end TauCeti

namespace MeasureTheory.MemLp

/-- A function in `Lᵖ` with `p ≠ 0` is finite almost everywhere. -/
theorem ae_enorm_lt_top {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp : p ≠ 0) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
    exact hx.trans_lt (eLpNormEssSup_le_eLpNorm_top.trans_lt hf.eLpNorm_lt_top)
  have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp hp_top hf.eLpNorm_lt_top
  filter_upwards [ae_lt_top' (hf.aestronglyMeasurable.enorm.pow_const _) hlt.ne] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos hp hp_top)).1 hx

end MeasureTheory.MemLp
