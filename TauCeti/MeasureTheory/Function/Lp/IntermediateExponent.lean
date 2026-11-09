/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `Lᵖ` membership at an intermediate exponent

A function lying in both `L^{p₀}` and `L^{p₁}` lies in `Lᵖ` for every `0 < p₀ ≤ p ≤ p₁`, on an
arbitrary measure space. Pointwise, `‖f‖ ^ p ≤ ‖f‖ ^ {p₀} + ‖f‖ ^ {p₁}` when `p₁` is finite,
according as `‖f‖ ≤ 1` or not, and `‖f‖ ^ p ≤ ‖f‖_∞ ^ {p - p₀} ‖f‖ ^ {p₀}` when `p₁ = ∞`.

This inclusion `L^{p₀} ∩ L^{p₁} ⊆ Lᵖ` for `0 < p₀ ≤ p ≤ p₁` is what lets an operator bounded
into two `Lᵖ` spaces be compared with its values in the intermediate space, as in the Riesz–Thorin
theorem. For `1 ≤ p₀` it is quantitative: `‖f‖_p ≤ 2 max (‖f‖_{p₀}, ‖f‖_{p₁})`
(`MeasureTheory.eLpNorm_le_two_mul_max_of_le_of_le`).

Dually, `Lᵖ ⊆ L^{p₀} + L^{p₁}` for `p₀ ≤ p ≤ p₁`: the restrictions of `f` to where `‖f‖` exceeds
`‖f‖_p` and to where it does not lie in `L^{p₀}` and in `L^{p₁}`, each with norm at most `‖f‖_p`
(`MeasureTheory.MemLp.exists_add_ae_eq_of_le_of_le`, and
`MeasureTheory.Lp.exists_add_ae_eq_of_le_of_le` for elements of `Lᵖ`). Together the two
inclusions make `Lᵖ` an intermediate space of the couple `(L^{p₀}, L^{p₁})`.
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

/-- `a ^ p = a ^ (p - q) * a ^ q` for `a ≠ 0, ∞`, so a bound on `a ^ (p - q)` trades the power `p`
for the power `q`. -/
private theorem rpow_le_rpow_sub_mul_rpow {a b : ℝ≥0∞} {p q : ℝ} (ha0 : a ≠ 0) (ha : a ≠ ∞)
    (h : a ^ (p - q) ≤ b ^ (p - q)) : a ^ p ≤ b ^ (p - q) * a ^ q := by
  rw [← sub_add_cancel p q, ENNReal.rpow_add _ _ ha0 ha, add_sub_cancel_right]
  gcongr

private theorem lintegral_rpow_enorm_eq_eLpNorm_rpow {f : α → E} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = eLpNorm f p μ ^ p.toReal := by
  rw [eLpNorm_eq_eLpNorm' hp0 hp hf,
    lintegral_rpow_enorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]

/-- If `∫ ‖k‖ ^ q ≤ t ^ q` then `‖k‖_q ≤ t`. -/
private theorem eLpNorm_le_of_lintegral_rpow_le {k : α → E} {q : ℝ≥0∞} {t : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hk : AEStronglyMeasurable k μ) (h : ∫⁻ x, ‖k x‖ₑ ^ q.toReal ∂μ ≤ t ^ q.toReal) :
    eLpNorm k q μ ≤ t := by
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [← ENNReal.rpow_le_rpow_iff hq', ← lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hk]
  exact h

/-- If `‖k x‖ ^ q ≤ t ^ (q - p) ‖f x‖ ^ p` pointwise, where `t = ‖f‖_p`, then `‖k‖_q ≤ t`. -/
private theorem eLpNorm_le_of_rpow_le_rpow_mul {f k : α → E} {p q : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hq0 : q ≠ 0) (hq : q ≠ ∞) (hf : AEStronglyMeasurable f μ)
    (hk : AEStronglyMeasurable k μ) (ht0 : eLpNorm f p μ ≠ 0) (ht : eLpNorm f p μ ≠ ∞)
    (hkf : ∀ x, ‖k x‖ₑ ^ q.toReal ≤
      eLpNorm f p μ ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal) :
    eLpNorm k q μ ≤ eLpNorm f p μ := by
  refine eLpNorm_le_of_lintegral_rpow_le hq0 hq hk ?_
  calc ∫⁻ x, ‖k x‖ₑ ^ q.toReal ∂μ
      ≤ ∫⁻ x, eLpNorm f p μ ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal ∂μ := lintegral_mono hkf
    _ = eLpNorm f p μ ^ (q.toReal - p.toReal) * eLpNorm f p μ ^ p.toReal := by
      rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero ht0 ht),
        lintegral_rpow_enorm_eq_eLpNorm_rpow hp0 hp hf]
    _ = eLpNorm f p μ ^ q.toReal := by rw [← ENNReal.rpow_add _ _ ht0 ht, sub_add_cancel]

/-- A function in `Lᵖ` is the sum of a function in `L^{p₀}` and a function in `L^{p₁}` for every
`p₀ ≤ p ≤ p₁`, each of norm at most `‖f‖_p`. This is the inclusion `Lᵖ ⊆ L^{p₀} + L^{p₁}`; the
two pieces are the restrictions of `f` to where `‖f‖` exceeds `‖f‖_p` and to where it does not. -/
theorem MemLp.exists_add_ae_eq_of_le_of_le {f : α → E} {p₀ p p₁ : ℝ≥0∞} (hf : MemLp f p μ)
    (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    ∃ g h : α → E, MemLp g p₀ μ ∧ eLpNorm g p₀ μ ≤ eLpNorm f p μ ∧
      MemLp h p₁ μ ∧ eLpNorm h p₁ μ ≤ eLpNorm f p μ ∧ g + h =ᵐ[μ] f := by
  rcases h₀.eq_or_lt with rfl | h₀
  · exact ⟨f, 0, hf, le_rfl, MemLp.zero, by simp, by simp⟩
  rcases h₁.eq_or_lt with rfl | h₁
  · exact ⟨0, f, MemLp.zero, by simp, hf, le_rfl, by simp⟩
  have hp0 : p ≠ 0 := (h₀.trans_le' bot_le).ne'
  have hp : p ≠ ∞ := h₁.ne_top
  have hp₁0 : p₁ ≠ 0 := (h₁.trans_le' bot_le).ne'
  rcases eq_or_ne (eLpNorm f p μ) 0 with ht0 | ht0
  · refine ⟨0, 0, MemLp.zero, by simp, MemLp.zero, by simp, ?_⟩
    simpa using ((eLpNorm_eq_zero_iff hp0).1 ht0).symm
  -- Split a strongly measurable representative `F` of `f` at the level `t = ‖f‖_p`.
  set F := hf.aestronglyMeasurable.mk f
  have hF : StronglyMeasurable F := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hFt : eLpNorm F p μ = eLpNorm f p μ :=
    eLpNorm_congr_ae hf.aestronglyMeasurable.ae_eq_mk.symm
  set t := eLpNorm f p μ
  have ht : t ≠ ∞ := hf.eLpNorm_ne_top
  set s := {x | t < ‖F x‖ₑ}
  have hs : MeasurableSet s := measurableSet_lt measurable_const hF.enorm
  have hg : eLpNorm (s.indicator F) p₀ μ ≤ t := by
    rcases eq_or_ne p₀ 0 with rfl | hp₀0
    · rw [eLpNorm_exponent_zero (hF.indicator hs).aestronglyMeasurable]
      exact zero_le
    rw [← hFt]
    refine eLpNorm_le_of_rpow_le_rpow_mul hp0 hp hp₀0 h₀.ne_top hF.aestronglyMeasurable
      (hF.indicator hs).aestronglyMeasurable (hFt ▸ ht0) (hFt ▸ ht) fun x => ?_
    rw [hFt]
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact rpow_le_rpow_sub_mul_rpow (hx.trans_le' bot_le).ne' enorm_ne_top
        (ENNReal.rpow_le_rpow_of_nonpos (le_of_lt hx)
          (sub_nonpos.2 (ENNReal.toReal_mono hp h₀.le)))
    · rw [Set.indicator_of_notMem hx, enorm_zero,
        ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp₀0 h₀.ne_top)]
      exact zero_le
  have hh : eLpNorm (sᶜ.indicator F) p₁ μ ≤ t := by
    rcases eq_or_ne p₁ ∞ with rfl | hp₁
    · rw [eLpNorm_exponent_top (hF.indicator hs.compl).aestronglyMeasurable]
      refine eLpNormEssSup_le_of_ae_enorm_bound (Filter.Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ sᶜ
      · rw [Set.indicator_of_mem hx]
        exact not_lt.1 hx
      · rw [Set.indicator_of_notMem hx, enorm_zero]
        exact zero_le
    rw [← hFt]
    refine eLpNorm_le_of_rpow_le_rpow_mul hp0 hp hp₁0 hp₁ hF.aestronglyMeasurable
      (hF.indicator hs.compl).aestronglyMeasurable (hFt ▸ ht0) (hFt ▸ ht) fun x => ?_
    rw [hFt]
    by_cases hx : x ∈ sᶜ ∧ F x ≠ 0
    · rw [Set.indicator_of_mem hx.1]
      exact rpow_le_rpow_sub_mul_rpow (enorm_ne_zero.2 hx.2) enorm_ne_top
        (ENNReal.rpow_le_rpow (not_lt.1 hx.1) (sub_nonneg.2 (ENNReal.toReal_mono hp₁ h₁.le)))
    · have : sᶜ.indicator F x = 0 := by
        by_cases hx' : x ∈ sᶜ
        · rw [Set.indicator_of_mem hx']
          exact not_not.1 fun h => hx ⟨hx', h⟩
        · exact Set.indicator_of_notMem hx' _
      rw [this, enorm_zero, ENNReal.zero_rpow_of_pos (ENNReal.toReal_pos hp₁0 hp₁)]
      exact zero_le
  refine ⟨s.indicator F, sᶜ.indicator F, hg.trans_lt hf.eLpNorm_lt_top, hg,
    hh.trans_lt hf.eLpNorm_lt_top, hh, ?_⟩
  rw [Set.indicator_self_add_compl]
  exact hf.aestronglyMeasurable.ae_eq_mk.symm

/-- Quantitative form of `MeasureTheory.MemLp.of_le_of_le`: for `1 ≤ p₀ ≤ p ≤ p₁`,
`‖f‖_p ≤ 2 max (‖f‖_{p₀}, ‖f‖_{p₁})`. Pointwise, with `M` the maximum,
`‖f‖ ^ p ≤ M ^ (p - p₀) ‖f‖ ^ {p₀} + M ^ (p - p₁) ‖f‖ ^ {p₁}` according as `‖f‖ ≤ M` or not. -/
theorem eLpNorm_le_two_mul_max_of_le_of_le {f : α → E} {p₀ p p₁ : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hp₀ : 1 ≤ p₀) (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    eLpNorm f p μ ≤ 2 * max (eLpNorm f p₀ μ) (eLpNorm f p₁ μ) := by
  set M := max (eLpNorm f p₀ μ) (eLpNorm f p₁ μ)
  have hM : M ≤ 2 * M := le_mul_of_one_le_left' one_le_two
  rcases h₀.eq_or_lt with rfl | h₀
  · exact (le_max_left _ _).trans hM
  rcases h₁.eq_or_lt with rfl | h₁
  · exact (le_max_right _ _).trans hM
  have hp₀0 : p₀ ≠ 0 := (zero_lt_one.trans_le hp₀).ne'
  have hp0 : p ≠ 0 := (h₀.trans_le' bot_le).ne'
  have hp : p ≠ ∞ := h₁.ne_top
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hp₀' : 0 < p₀.toReal := ENNReal.toReal_pos hp₀0 h₀.ne_top
  have hle₀ : p₀.toReal ≤ p.toReal := ENNReal.toReal_mono hp h₀.le
  rcases eq_or_ne M ∞ with hMt | hMt
  · simp [hMt]
  rcases eq_or_ne M 0 with hM0 | hM0
  · have hf0 : f =ᵐ[μ] 0 :=
      (eLpNorm_eq_zero_iff hp₀0).1 (le_antisymm (hM0 ▸ le_max_left _ _) bot_le)
    rw [eLpNorm_congr_ae hf0, eLpNorm_zero]
    exact zero_le
  have h₀M : eLpNorm f p₀ μ ≤ M := le_max_left _ _
  have h₁M : eLpNorm f p₁ μ ≤ M := le_max_right _ _
  -- The contribution of the set where `‖f‖ ≤ M`, measured in `L^{p₀}`, is at most `M ^ p`.
  have hI₀ : ∫⁻ x, M ^ (p.toReal - p₀.toReal) * ‖f x‖ₑ ^ p₀.toReal ∂μ ≤ M ^ p.toReal := by
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hM0 hMt),
      lintegral_rpow_enorm_eq_eLpNorm_rpow hp₀0 h₀.ne_top hf]
    calc M ^ (p.toReal - p₀.toReal) * eLpNorm f p₀ μ ^ p₀.toReal
        ≤ M ^ (p.toReal - p₀.toReal) * M ^ p₀.toReal := by gcongr
      _ = M ^ p.toReal := by rw [← ENNReal.rpow_add _ _ hM0 hMt, sub_add_cancel]
  refine eLpNorm_le_of_lintegral_rpow_le hp0 hp hf ?_
  have h2 : (2 : ℝ≥0∞) ≤ 2 ^ p.toReal := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_le one_le_two
      (show (1 : ℝ) ≤ p.toReal by simpa using ENNReal.toReal_mono hp (hp₀.trans h₀.le))
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp'.le]
  refine le_trans ?_ ((two_mul _).symm.trans_le (by gcongr))
  rcases eq_or_ne p₁ ∞ with rfl | hp₁
  · -- `‖f‖ ≤ ‖f‖_∞ ≤ M` almost everywhere.
    refine le_add_right (le_trans (lintegral_mono_ae ?_) hI₀)
    filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
    rw [← eLpNorm_exponent_top hf] at hx
    rcases eq_or_ne ‖f x‖ₑ 0 with h0 | h0
    · rw [h0, ENNReal.zero_rpow_of_pos hp', ENNReal.zero_rpow_of_pos hp₀', mul_zero]
    exact rpow_le_rpow_sub_mul_rpow h0 enorm_ne_top
      (ENNReal.rpow_le_rpow (hx.trans h₁M) (sub_nonneg.2 hle₀))
  have hp₁0 : p₁ ≠ 0 := (h₁.trans_le' bot_le).ne'
  have hle₁ : p.toReal ≤ p₁.toReal := ENNReal.toReal_mono hp₁ h₁.le
  have hI₁ : ∫⁻ x, M ^ (p.toReal - p₁.toReal) * ‖f x‖ₑ ^ p₁.toReal ∂μ ≤ M ^ p.toReal := by
    rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hM0 hMt),
      lintegral_rpow_enorm_eq_eLpNorm_rpow hp₁0 hp₁ hf]
    calc M ^ (p.toReal - p₁.toReal) * eLpNorm f p₁ μ ^ p₁.toReal
        ≤ M ^ (p.toReal - p₁.toReal) * M ^ p₁.toReal := by gcongr
      _ = M ^ p.toReal := by rw [← ENNReal.rpow_add _ _ hM0 hMt, sub_add_cancel]
  refine le_trans ?_ (add_le_add hI₀ hI₁)
  rw [← lintegral_add_left' ((hf.enorm.pow_const _).const_mul _)]
  refine lintegral_mono fun x => ?_
  rcases eq_or_ne ‖f x‖ₑ 0 with h0 | h0
  · rw [h0, ENNReal.zero_rpow_of_pos hp']
    exact zero_le
  rcases le_total ‖f x‖ₑ M with hx | hx
  · exact le_add_right (rpow_le_rpow_sub_mul_rpow h0 enorm_ne_top
      (ENNReal.rpow_le_rpow hx (sub_nonneg.2 hle₀)))
  · exact le_add_left (rpow_le_rpow_sub_mul_rpow h0 enorm_ne_top
      (ENNReal.rpow_le_rpow_of_nonpos hx (sub_nonpos.2 hle₁)))

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
