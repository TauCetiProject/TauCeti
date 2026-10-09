/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `Lᵖ` membership at an intermediate exponent

A function lying in both `L^{p₀}` and `L^{p₁}` lies in `Lᵖ` for every `p` between them, on an
arbitrary measure space. Pointwise, `‖f‖ ^ p ≤ ‖f‖ ^ {p₀} + ‖f‖ ^ {p₁}` when `p₁` is finite,
according as `‖f‖ ≤ 1` or not, and `‖f‖ ^ p ≤ ‖f‖_∞ ^ {p - p₀} ‖f‖ ^ {p₀}` when `p₁ = ∞`.

This inclusion `L^{p₀} ∩ L^{p₁} ⊆ Lᵖ` is what lets an operator bounded into two `Lᵖ` spaces be
compared with its values in the intermediate space, as in the Riesz–Thorin theorem.
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {α ε : Type*} {mα : MeasurableSpace α} {μ : Measure α} [TopologicalSpace ε]
  [ContinuousENorm ε]

/-- A function in `L^{p₀}` and in `L^{p₁}` is in `Lᵖ` for every `p₀ ≤ p ≤ p₁`, provided
`p₀ ≠ 0`. -/
theorem MemLp.of_le_of_le {f : α → ε} {p₀ p p₁ : ℝ≥0∞} (hf₀ : MemLp f p₀ μ)
    (hf₁ : MemLp f p₁ μ) (hp₀ : p₀ ≠ 0) (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) : MemLp f p μ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · rwa [top_le_iff.1 h₁] at hf₁
  have hp₀' : p₀ ≠ ∞ := ne_top_of_le_ne_top hp h₀
  have hp0 : p ≠ 0 := (pos_iff_ne_zero.2 hp₀ |>.trans_le h₀).ne'
  have hmeas := hf₀.aestronglyMeasurable
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp hmeas).2 ?_
  have hI₀ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hp₀' hf₀.eLpNorm_lt_top
  have hle : p₀.toReal ≤ p.toReal := ENNReal.toReal_mono hp h₀
  rcases eq_or_ne p₁ ∞ with rfl | hp₁
  · -- `f` is essentially bounded by `C`, so `‖f‖ ^ p ≤ C ^ (p - p₀) * ‖f‖ ^ p₀`.
    set C := eLpNormEssSup f μ
    have hC : C ≠ ∞ := by
      simpa [C, eLpNorm_exponent_top hmeas] using hf₁.eLpNorm_lt_top.ne
    calc ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ
        ≤ ∫⁻ a, C ^ (p.toReal - p₀.toReal) * ‖f a‖ₑ ^ p₀.toReal ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with a ha
          calc ‖f a‖ₑ ^ p.toReal = ‖f a‖ₑ ^ (p.toReal - p₀.toReal) * ‖f a‖ₑ ^ p₀.toReal := by
                rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) ENNReal.toReal_nonneg,
                  sub_add_cancel]
            _ ≤ C ^ (p.toReal - p₀.toReal) * ‖f a‖ₑ ^ p₀.toReal := by
                gcongr
      _ < ∞ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hC)]
        exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by linarith) hC) hI₀
  · -- `‖f‖ ^ p` is dominated by `‖f‖ ^ p₀` where `‖f‖ ≤ 1` and by `‖f‖ ^ p₁` elsewhere.
    have hI₁ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (pos_iff_ne_zero.1 ((pos_iff_ne_zero.2 hp0).trans_le h₁)) hp₁ hf₁.eLpNorm_lt_top
    have hle₁ : p.toReal ≤ p₁.toReal := ENNReal.toReal_mono hp₁ h₁
    calc ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ
        ≤ ∫⁻ a, ‖f a‖ₑ ^ p₀.toReal + ‖f a‖ₑ ^ p₁.toReal ∂μ := by
          refine lintegral_mono fun a => ?_
          rcases le_total ‖f a‖ₑ 1 with h | h
          · exact (ENNReal.rpow_le_rpow_of_exponent_ge h hle).trans le_self_add
          · exact (ENNReal.rpow_le_rpow_of_exponent_le h hle₁).trans le_add_self
      _ < ∞ := by
        rw [lintegral_add_left' (hmeas.enorm.pow_const _)]
        exact ENNReal.add_lt_top.2 ⟨hI₀, hI₁⟩

end MeasureTheory
