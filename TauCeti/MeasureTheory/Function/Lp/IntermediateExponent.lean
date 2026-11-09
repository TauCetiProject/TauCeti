/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# `Lᵖ` membership at an intermediate exponent

A function lying in both `L^{p₀}` and `L^{p₁}` lies in `Lᵖ` for every `0 < p₀ ≤ p ≤ p₁`, on an
arbitrary measure space. Pointwise, `‖f‖ ^ p ≤ ‖f‖ ^ {p₀} + ‖f‖ ^ {p₁}` when `p₁` is finite,
according as `‖f‖ ≤ 1` or not, and `‖f‖ ^ p ≤ ‖f‖_∞ ^ {p - p₀} ‖f‖ ^ {p₀}` when `p₁ = ∞`.

This inclusion `L^{p₀} ∩ L^{p₁} ⊆ Lᵖ` for `0 < p₀ ≤ p ≤ p₁` is what lets an operator bounded
into two `Lᵖ` spaces be compared with its values in the intermediate space, as in the Riesz–Thorin
theorem.

When `p₁ = ∞` the same pointwise bound gives the quantitative form
`‖f‖_q ≤ ‖f‖_∞ ^ (1 - p / q) ‖f‖_p ^ (p / q)` for `0 < p ≤ q`
(`MeasureTheory.eLpNorm_le_eLpNorm_top_rpow_mul_eLpNorm_rpow`), the interpolation inequality
used to pass from an `Lᵖ` and an `L^∞` bound to an `L^q` bound.
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
  have hp0 : p ≠ 0 := (hp₀.bot_lt.trans_le h₀).ne'
  have hmeas := hf₀.aestronglyMeasurable
  refine (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hp hmeas).2 ?_
  have hI₀ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ (ne_top_of_le_ne_top hp h₀)
    hf₀.eLpNorm_lt_top
  have hle : p₀.toReal ≤ p.toReal := ENNReal.toReal_mono hp h₀
  rcases eq_or_ne p₁ ∞ with rfl | hp₁
  · -- `f` is essentially bounded by `C`, so `‖f‖ ^ p ≤ C ^ (p - p₀) * ‖f‖ ^ p₀`.
    set C := eLpNormEssSup f μ
    have hC : C ≠ ∞ := by simpa [C, eLpNorm_exponent_top hmeas] using hf₁.eLpNorm_lt_top.ne
    have hr : 0 ≤ p.toReal - p₀.toReal := sub_nonneg.2 hle
    calc ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ
        ≤ ∫⁻ a, C ^ (p.toReal - p₀.toReal) * ‖f a‖ₑ ^ p₀.toReal ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with a ha
          calc ‖f a‖ₑ ^ p.toReal = ‖f a‖ₑ ^ (p.toReal - p₀.toReal) * ‖f a‖ₑ ^ p₀.toReal := by
                rw [← ENNReal.rpow_add_of_nonneg _ _ hr ENNReal.toReal_nonneg, sub_add_cancel]
            _ ≤ C ^ (p.toReal - p₀.toReal) * ‖f a‖ₑ ^ p₀.toReal := by gcongr
      _ < ∞ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hr hC)]
        exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hr hC) hI₀
  · -- `‖f‖ ^ p` is dominated by `‖f‖ ^ p₀` where `‖f‖ ≤ 1` and by `‖f‖ ^ p₁` elsewhere.
    have hI₁ := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (hp0.bot_lt.trans_le h₁).ne' hp₁ hf₁.eLpNorm_lt_top
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

/-- **Interpolation of `Lᵖ` norms against `L^∞`.** For `0 < p ≤ q`,
`‖f‖_q ≤ ‖f‖_∞ ^ (1 - p / q) ‖f‖_p ^ (p / q)`. The exponents are computed with `ENNReal.toReal`,
so `p / q` reads as `0` when `q = ∞`, where the inequality is an equality. -/
theorem eLpNorm_le_eLpNorm_top_rpow_mul_eLpNorm_rpow {f : α → ε} {p q : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hp0 : p ≠ 0) (hpq : p ≤ q) :
    eLpNorm f q μ ≤
      eLpNorm f ∞ μ ^ (1 - p.toReal / q.toReal) * eLpNorm f p μ ^ (p.toReal / q.toReal) := by
  rcases eq_or_ne q ∞ with rfl | hq
  · simp
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hq0 : q ≠ 0 := (hp0.bot_lt.trans_le hpq).ne'
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hs : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hrs : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq hpq
  set C := eLpNormEssSup f μ
  set I := ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ
  -- Pointwise `‖f‖ ^ q ≤ C ^ (q - p) ‖f‖ ^ p`, as in `MemLp.of_le_of_le`.
  have hint : ∫⁻ a, ‖f a‖ₑ ^ q.toReal ∂μ ≤ C ^ (q.toReal - p.toReal) * I := by
    rw [← lintegral_const_mul'' _ (hf.enorm.pow_const _)]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with a ha
    calc ‖f a‖ₑ ^ q.toReal = ‖f a‖ₑ ^ (q.toReal - p.toReal) * ‖f a‖ₑ ^ p.toReal := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hrs) hr.le, sub_add_cancel]
      _ ≤ C ^ (q.toReal - p.toReal) * ‖f a‖ₑ ^ p.toReal := by gcongr
  rw [eLpNorm_exponent_top hf, eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hq hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp hf, ← ENNReal.rpow_mul]
  calc (∫⁻ a, ‖f a‖ₑ ^ q.toReal ∂μ) ^ (1 / q.toReal)
      ≤ (C ^ (q.toReal - p.toReal) * I) ^ (1 / q.toReal) := by gcongr
    _ = C ^ (1 - p.toReal / q.toReal) * I ^ (1 / p.toReal * (p.toReal / q.toReal)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
        congr 2 <;> field_simp

end MeasureTheory
