/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `Lᵖ` membership at an intermediate exponent

A function lying in both `L^{p₀}` and `L^{p₁}` lies in `Lᵖ` for every `0 < p₀ ≤ p ≤ p₁`, on an
arbitrary measure space. Pointwise, `‖f‖ ^ p ≤ ‖f‖ ^ {p₀} + ‖f‖ ^ {p₁}` when `p₁` is finite,
according as `‖f‖ ≤ 1` or not, and `‖f‖ ^ p ≤ ‖f‖_∞ ^ {p - p₀} ‖f‖ ^ {p₀}` when `p₁ = ∞`.

This inclusion `L^{p₀} ∩ L^{p₁} ⊆ Lᵖ` for `0 < p₀ ≤ p ≤ p₁` is what lets an operator bounded
into two `Lᵖ` spaces be compared with its values in the intermediate space, as in the Riesz–Thorin
theorem. It is quantitative: `‖f‖_p ≤ max (‖f‖_{p₀}, ‖f‖_{p₁})`
(`MeasureTheory.eLpNorm_le_max_of_le_of_le`). With `M` this maximum, `‖f‖ ^ p` is at most
`M ^ (p - p₀) ‖f‖ ^ {p₀}` almost everywhere when `p₁ = ∞`; for finite `p₁`, writing
`p = (1 - θ) p₀ + θ p₁`, the weighted AM-GM inequality bounds it by
`(1 - θ) M ^ (p - p₀) ‖f‖ ^ {p₀} + θ M ^ (p - p₁) ‖f‖ ^ {p₁}`. Either way the integral is at most
`M ^ p`.

Dually, `Lᵖ ⊆ L^{p₀} + L^{p₁}` for `p₀ ≤ p ≤ p₁`: every `f ∈ Lᵖ` is almost everywhere a sum `g + h`
with `‖g‖_{p₀} ≤ ‖f‖_p` and `‖h‖_{p₁} ≤ ‖f‖_p` (`MeasureTheory.MemLp.exists_add_ae_eq_of_le_of_le`,
and `MeasureTheory.Lp.exists_add_ae_eq_of_le_of_le` for elements of `Lᵖ`). The part of `f` where
`‖f‖` exceeds `‖f‖_p` and the part where it does not are such a pair
(`MeasureTheory.eLpNorm_indicator_eLpNorm_lt_enorm_le`,
`MeasureTheory.eLpNorm_indicator_enorm_le_eLpNorm_le`). Together the two inclusions make `Lᵖ` an
intermediate space of the couple `(L^{p₀}, L^{p₁})`.
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

section Split

variable {E : Type*} [NormedAddCommGroup E]

/-- For `p ≠ 0, ∞`, the integral of `‖f‖ₑ ^ p` is the `p`-th power of the `Lᵖ` seminorm of `f`. -/
theorem lintegral_rpow_enorm_eq_eLpNorm_rpow {f : α → E} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = eLpNorm f p μ ^ p.toReal := by
  rw [eLpNorm_eq_eLpNorm' hp0 hp hf,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]

/-- If `∫ ‖k‖ ^ q ≤ t ^ q` then `‖k‖_q ≤ t`. -/
theorem eLpNorm_le_of_lintegral_rpow_le {k : α → E} {q : ℝ≥0∞} {t : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hk : AEStronglyMeasurable k μ) (h : ∫⁻ x, ‖k x‖ₑ ^ q.toReal ∂μ ≤ t ^ q.toReal) :
    eLpNorm k q μ ≤ t := by
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [← ENNReal.rpow_le_rpow_iff hq', ← lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hk]
  exact h

/-- If `‖f‖_q ≤ M` for `M ≠ 0, ∞`, then `∫ M ^ (r - q) ‖f‖ ^ q ≤ M ^ r` for every real `r`. -/
theorem lintegral_rpow_sub_mul_rpow_enorm_le {f : α → E} {q M : ℝ≥0∞} (r : ℝ) (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hM0 : M ≠ 0) (hM : M ≠ ∞) (hf : AEStronglyMeasurable f μ)
    (hfM : eLpNorm f q μ ≤ M) :
    ∫⁻ x, M ^ (r - q.toReal) * ‖f x‖ₑ ^ q.toReal ∂μ ≤ M ^ r := by
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hM0 hM),
    lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hf]
  calc M ^ (r - q.toReal) * eLpNorm f q μ ^ q.toReal
      ≤ M ^ (r - q.toReal) * M ^ q.toReal := by gcongr
    _ = M ^ r := by rw [← ENNReal.rpow_add _ _ hM0 hM, sub_add_cancel]

/-- If `‖k x‖ ^ q ≤ t ^ (q - p) ‖f x‖ ^ p` pointwise, where `t = ‖f‖_p`, then `‖k‖_q ≤ t`. -/
theorem eLpNorm_le_of_rpow_le_rpow_mul {f k : α → E} {p q : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hq0 : q ≠ 0) (hq : q ≠ ∞) (hf : AEStronglyMeasurable f μ)
    (hk : AEStronglyMeasurable k μ) (ht0 : eLpNorm f p μ ≠ 0) (ht : eLpNorm f p μ ≠ ∞)
    (hkf : ∀ x, ‖k x‖ₑ ^ q.toReal ≤
      eLpNorm f p μ ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal) :
    eLpNorm k q μ ≤ eLpNorm f p μ :=
  eLpNorm_le_of_lintegral_rpow_le hq0 hq hk <| (lintegral_mono hkf).trans <|
    lintegral_rpow_sub_mul_rpow_enorm_le _ hp0 hp ht0 ht hf le_rfl

/-- For `p₀ ≤ p < ∞`, the part of `f` where `‖f‖` exceeds `‖f‖_p` has `L^{p₀}` norm at most
`‖f‖_p`. -/
theorem eLpNorm_indicator_eLpNorm_lt_enorm_le {f : α → E} {p₀ p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (h₀ : p₀ ≤ p) (hp : p ≠ ∞) :
    eLpNorm ({x | eLpNorm f p μ < ‖f x‖ₑ}.indicator f) p₀ μ ≤ eLpNorm f p μ := by
  set t := eLpNorm f p μ
  set s := {x | t < ‖f x‖ₑ}
  have hs₀ : NullMeasurableSet s μ := nullMeasurableSet_lt aemeasurable_const hf.enorm
  have hs : AEStronglyMeasurable (s.indicator f) μ := hf.indicator₀ hs₀
  rcases eq_or_ne p₀ 0 with rfl | hp₀0
  · rw [eLpNorm_exponent_zero hs]
    exact zero_le
  have hp0 : p ≠ 0 := (hp₀0.bot_lt.trans_le h₀).ne'
  rcases eq_or_ne t 0 with ht0 | ht0
  · -- `f` vanishes almost everywhere, hence so does its restriction.
    refine (eLpNorm_indicator_le f hs₀).trans_eq ?_
    rw [eLpNorm_congr_ae ((eLpNorm_eq_zero_iff hp0).1 ht0), eLpNorm_zero, ht0]
  rcases eq_or_ne t ∞ with ht | ht
  · exact ht ▸ le_top
  refine eLpNorm_le_of_rpow_le_rpow_mul hp0 hp hp₀0 (ne_top_of_le_ne_top hp h₀) hf hs ht0 ht
    fun x => ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    exact ENNReal.rpow_le_rpow_sub_mul_rpow (hx.trans_le' bot_le).ne' enorm_ne_top
      (ENNReal.rpow_le_rpow_of_nonpos (le_of_lt hx) (sub_nonpos.2 (ENNReal.toReal_mono hp h₀)))
  · rw [Set.indicator_of_notMem hx, enorm_zero,
      ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp₀0 (ne_top_of_le_ne_top hp h₀))]
    exact zero_le

/-- For `p ≤ p₁`, the part of `f` where `‖f‖` is at most `‖f‖_p` has `L^{p₁}` norm at most
`‖f‖_p`. -/
theorem eLpNorm_indicator_enorm_le_eLpNorm_le {f : α → E} {p p₁ : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (h₁ : p ≤ p₁) :
    eLpNorm ({x | ‖f x‖ₑ ≤ eLpNorm f p μ}.indicator f) p₁ μ ≤ eLpNorm f p μ := by
  set t := eLpNorm f p μ
  set s := {x | ‖f x‖ₑ ≤ t}
  have hs : AEStronglyMeasurable (s.indicator f) μ :=
    hf.indicator₀ (nullMeasurableSet_le hf.enorm aemeasurable_const)
  have hst (x : α) : ‖s.indicator f x‖ₑ ≤ t := by
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact hx
    · rw [Set.indicator_of_notMem hx, enorm_zero]
      exact zero_le
  rcases eq_or_ne p₁ ∞ with rfl | hp₁
  · rw [eLpNorm_exponent_top hs]
    exact eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall hst)
  have hp : p ≠ ∞ := ne_top_of_le_ne_top hp₁ h₁
  rcases eq_or_ne t 0 with ht0 | ht0
  · -- `s.indicator f` vanishes identically.
    have h0 : s.indicator f = 0 :=
      funext fun x => enorm_eq_zero.1 (le_antisymm (ht0 ▸ hst x) bot_le)
    rw [h0, eLpNorm_zero, ht0]
  rcases eq_or_ne t ∞ with ht | ht
  · exact ht ▸ le_top
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact ht0 (eLpNorm_exponent_zero hf)
  have hp₁0 : p₁ ≠ 0 := (hp0.bot_lt.trans_le h₁).ne'
  refine eLpNorm_le_of_rpow_le_rpow_mul hp0 hp hp₁0 hp₁ hf hs ht0 ht fun x => ?_
  by_cases hx : x ∈ s ∧ f x ≠ 0
  · rw [Set.indicator_of_mem hx.1]
    exact ENNReal.rpow_le_rpow_sub_mul_rpow (enorm_ne_zero.2 hx.2) enorm_ne_top
      (ENNReal.rpow_le_rpow hx.1 (sub_nonneg.2 (ENNReal.toReal_mono hp₁ h₁)))
  · have : s.indicator f x = 0 := by
      by_cases hx' : x ∈ s
      · rw [Set.indicator_of_mem hx']
        exact not_not.1 fun h => hx ⟨hx', h⟩
      · exact Set.indicator_of_notMem hx' _
    rw [this, enorm_zero, ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp₁0 hp₁)]
    exact zero_le

/-- A function in `Lᵖ` is the sum of a function in `L^{p₀}` and a function in `L^{p₁}` for every
`p₀ ≤ p ≤ p₁`, each of norm at most `‖f‖_p`. This is the inclusion `Lᵖ ⊆ L^{p₀} + L^{p₁}`. -/
theorem MemLp.exists_add_ae_eq_of_le_of_le {f : α → E} {p₀ p p₁ : ℝ≥0∞} (hf : MemLp f p μ)
    (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    ∃ g h : α → E, MemLp g p₀ μ ∧ eLpNorm g p₀ μ ≤ eLpNorm f p μ ∧
      MemLp h p₁ μ ∧ eLpNorm h p₁ μ ≤ eLpNorm f p μ ∧ g + h =ᵐ[μ] f := by
  rcases eq_or_ne p ∞ with rfl | hp
  · obtain rfl := top_le_iff.1 h₁
    exact ⟨0, f, MemLp.zero, by simp, hf, le_rfl, by simp⟩
  -- Split `f` at the level `‖f‖_p`.
  have hf' := hf.aestronglyMeasurable
  have hg := eLpNorm_indicator_eLpNorm_lt_enorm_le hf' h₀ hp
  have hh := eLpNorm_indicator_enorm_le_eLpNorm_le hf' h₁
  refine ⟨_, _, hg.trans_lt hf.eLpNorm_lt_top, hg, hh.trans_lt hf.eLpNorm_lt_top, hh,
    Filter.Eventually.of_forall fun x => ?_⟩
  by_cases hx : eLpNorm f p μ < ‖f x‖ₑ
  · simp [hx, not_le.2 hx]
  · simp [hx, not_lt.1 hx]

/-- The `Lᵖ` norm at an intermediate exponent `p₀ ≤ p ≤ p₁`, with `p₀ ≠ 0`, is at most the
larger of the `L^{p₀}` and `L^{p₁}` norms: `‖f‖_p ≤ max (‖f‖_{p₀}, ‖f‖_{p₁})`. This is the
quantitative form of `MeasureTheory.MemLp.of_le_of_le`. -/
theorem eLpNorm_le_max_of_le_of_le {f : α → E} {p₀ p p₁ : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hp₀ : p₀ ≠ 0) (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    eLpNorm f p μ ≤ max (eLpNorm f p₀ μ) (eLpNorm f p₁ μ) := by
  set M := max (eLpNorm f p₀ μ) (eLpNorm f p₁ μ)
  rcases h₀.eq_or_lt with rfl | h₀
  · exact le_max_left _ _
  rcases h₁.eq_or_lt with rfl | h₁
  · exact le_max_right _ _
  have hp0 : p ≠ 0 := (h₀.trans_le' bot_le).ne'
  have hp : p ≠ ∞ := h₁.ne_top
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hle₀ : p₀.toReal ≤ p.toReal := ENNReal.toReal_mono hp h₀.le
  rcases eq_or_ne M ∞ with hMt | hMt
  · simp [hMt]
  rcases eq_or_ne M 0 with hM0 | hM0
  · have hf0 : f =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff hp₀).1 (le_antisymm (hM0 ▸ le_max_left _ _) bot_le)
    rw [eLpNorm_congr_ae hf0, eLpNorm_zero]
    exact zero_le
  have hI₀ := lintegral_rpow_sub_mul_rpow_enorm_le p.toReal hp₀ h₀.ne_top hM0 hMt hf
    (le_max_left _ _)
  refine eLpNorm_le_of_lintegral_rpow_le hp0 hp hf ?_
  rcases eq_or_ne p₁ ∞ with rfl | hp₁
  · -- `‖f‖ ≤ ‖f‖_∞ ≤ M` almost everywhere, so `‖f‖ ^ p ≤ M ^ (p - p₀) ‖f‖ ^ p₀`.
    refine le_trans (lintegral_mono_ae ?_) hI₀
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
    rw [← eLpNorm_exponent_top hf] at hx
    rcases eq_or_ne ‖f x‖ₑ 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos hp']
      exact zero_le
    exact ENNReal.rpow_le_rpow_sub_mul_rpow h0 enorm_ne_top
      (ENNReal.rpow_le_rpow (hx.trans (le_max_right _ _)) (sub_nonneg.2 hle₀))
  -- Write `p = (1 - θ) p₀ + θ p₁` and dominate `‖f‖ ^ p` by the corresponding combination of
  -- `M ^ (p - p₀) ‖f‖ ^ p₀` and `M ^ (p - p₁) ‖f‖ ^ p₁`, each integrating to at most `M ^ p`.
  have hp₁0 : p₁ ≠ 0 := (h₁.trans_le' bot_le).ne'
  have hlt₀ : p₀.toReal < p.toReal := ENNReal.toReal_strict_mono hp h₀
  have hlt₁ : p.toReal < p₁.toReal := ENNReal.toReal_strict_mono hp₁ h₁
  set θ := (p.toReal - p₀.toReal) / (p₁.toReal - p₀.toReal)
  have hθ₀ : 0 ≤ θ := div_nonneg (sub_nonneg.2 hle₀) (sub_nonneg.2 (hlt₀.trans hlt₁).le)
  have hθ₁ : θ ≤ 1 := (div_le_one (sub_pos.2 (hlt₀.trans hlt₁))).2 (by linarith)
  have hθ : (1 - θ) * p₀.toReal + θ * p₁.toReal = p.toReal := by
    simp only [θ]
    field_simp [(sub_pos.2 (hlt₀.trans hlt₁)).ne']
    ring
  have hI₁ := lintegral_rpow_sub_mul_rpow_enorm_le p.toReal hp₁0 hp₁ hM0 hMt hf
    (le_max_right _ _)
  calc ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ
      ≤ ∫⁻ x, ENNReal.ofReal (1 - θ) * (M ^ (p.toReal - p₀.toReal) * ‖f x‖ₑ ^ p₀.toReal) +
          ENNReal.ofReal θ * (M ^ (p.toReal - p₁.toReal) * ‖f x‖ₑ ^ p₁.toReal) ∂μ := by
        refine lintegral_mono fun x => ?_
        rcases eq_or_ne ‖f x‖ₑ 0 with h0 | h0
        · rw [h0, ENNReal.zero_rpow_of_pos hp']
          exact zero_le
        exact ENNReal.rpow_le_ofReal_mul_add_ofReal_mul hθ₀ hθ₁ hθ h0 enorm_ne_top hM0 hMt
    _ ≤ ENNReal.ofReal (1 - θ) * M ^ p.toReal + ENNReal.ofReal θ * M ^ p.toReal := by
        rw [lintegral_add_left' (((hf.enorm.pow_const _).const_mul _).const_mul _),
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        gcongr
    _ = M ^ p.toReal := by
        rw [← add_mul, ← ENNReal.ofReal_add (sub_nonneg.2 hθ₁) hθ₀, sub_add_cancel,
          ENNReal.ofReal_one, one_mul]

/-- An element of `Lᵖ` is the sum of an element of `L^{p₀}` and an element of `L^{p₁}` for every
`p₀ ≤ p ≤ p₁`, each of norm at most `‖f‖_p`. -/
theorem Lp.exists_add_ae_eq_of_le_of_le {p₀ p p₁ : ℝ≥0∞} (f : Lp E p μ) (h₀ : p₀ ≤ p)
    (h₁ : p ≤ p₁) :
    ∃ (g : Lp E p₀ μ) (h : Lp E p₁ μ), ⇑g + ⇑h =ᵐ[μ] f ∧ ‖g‖ ≤ ‖f‖ ∧ ‖h‖ ≤ ‖f‖ := by
  obtain ⟨g, h, hg, hgf, hh, hhf, hgh⟩ := (Lp.memLp f).exists_add_ae_eq_of_le_of_le h₀ h₁
  refine ⟨hg.toLp g, hh.toLp h, ?_, ?_, ?_⟩
  · filter_upwards [hg.coeFn_toLp, hh.coeFn_toLp, hgh] with a ha hb hab
    rw [Pi.add_apply, ha, hb]
    exact hab
  · rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hgf
  · rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) hhf

end Split

end MeasureTheory
