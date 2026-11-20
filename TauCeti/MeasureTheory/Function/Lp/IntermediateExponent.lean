/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal

/-!
# `Lᵖ` membership at an intermediate exponent

A function lying in both `L^{p₀}` and `L^{p₁}` lies in `Lᵖ` for every `0 < p₀ ≤ p ≤ p₁`, on an
arbitrary measure space. Pointwise, `‖f‖ ^ p ≤ ‖f‖ ^ {p₀} + ‖f‖ ^ {p₁}` when `p₁` is finite,
according as `‖f‖ ≤ 1` or not, and `‖f‖ ^ p ≤ ‖f‖_∞ ^ {p - p₀} ‖f‖ ^ {p₀}` when `p₁ = ∞`.

This inclusion `L^{p₀} ∩ L^{p₁} ⊆ Lᵖ` for `0 < p₀ ≤ p ≤ p₁` is what lets an operator bounded
into two `Lᵖ` spaces be compared with its values in the intermediate space, as in the Riesz–Thorin
theorem.

Quantitatively, the `Lᵖ` norms are logarithmically convex in `1 / p`: if
`1 / p = (1 - θ) / p₀ + θ / p₁` with `0 ≤ θ ≤ 1`, then

`‖f‖_p ≤ ‖f‖_{p₀} ^ (1 - θ) ‖f‖_{p₁} ^ θ`

(`MeasureTheory.eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow`), by Hölder's inequality applied to
`‖f‖ = ‖f‖ ^ (1 - θ) ‖f‖ ^ θ`. The same bound for elements of `Lᵖ` spaces representing one
function is `MeasureTheory.Lp.norm_le_norm_rpow_mul_norm_rpow_of_ae_eq`. Since the exponent
`1 - θ` is positive for `θ < 1`, smallness in `L^{p₀}` and boundedness in `L^{p₁}` give smallness
in `Lᵖ`; this is how compactness into `L^{p₀}` passes to the intermediate exponents.

A cruder bound needs no interpolation parameter: `‖f‖_p ≤ max (‖f‖_{p₀}, ‖f‖_{p₁})`
(`MeasureTheory.eLpNorm_le_max_of_le_of_le`), from logarithmic convexity since
`‖f‖_{p₀} ^ (1 - θ) ‖f‖_{p₁} ^ θ` is at most the maximum.

Dually, `Lᵖ ⊆ L^{p₀} + L^{p₁}` for `p₀ ≤ p ≤ p₁`: every `f ∈ Lᵖ` is almost everywhere a sum `g + h`
with `‖g‖_{p₀} ≤ ‖f‖_p` and `‖h‖_{p₁} ≤ ‖f‖_p` (`MeasureTheory.MemLp.exists_add_ae_eq_of_le_of_le`,
and `MeasureTheory.Lp.exists_add_ae_eq_of_le_of_le` for elements of `Lᵖ`). The part of `f` where
`‖f‖` exceeds `‖f‖_p` and the part where it does not are such a pair
(`MeasureTheory.eLpNorm_indicator_eLpNorm_lt_enorm_le`,
`MeasureTheory.eLpNorm_indicator_enorm_le_eLpNorm_le`). Together the two inclusions make `Lᵖ` an
intermediate space of the couple `(L^{p₀}, L^{p₁})`.

## References

* G. B. Folland, *Real Analysis*, 2nd ed., Proposition 6.10.
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
  refine (eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp0 hp hmeas).2 ?_
  have hI₀ := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp₀ (ne_top_of_le_ne_top hp h₀)
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
    have hI₁ := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top
      (hp0.bot_lt.trans_le h₁).ne' hp₁ hf₁.eLpNorm_lt_top
    have hle₁ : p.toReal ≤ p₁.toReal := ENNReal.toReal_mono hp₁ h₁
    calc ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ
        ≤ ∫⁻ a, ‖f a‖ₑ ^ p₀.toReal + ‖f a‖ₑ ^ p₁.toReal ∂μ := by
          refine lintegral_mono fun a => ?_
          rcases le_total ‖f a‖ₑ 1 with h | h
          · exact (ENNReal.rpow_le_rpow_of_exponent_ge h hle).trans le_self_add
          · exact (ENNReal.rpow_le_rpow_of_exponent_le h hle₁).trans le_add_self
      _ < ∞ := by
        rw [lintegral_add_left' (hmeas.eNorm.pow_const _)]
        exact ENNReal.add_lt_top.2 ⟨hI₀, hI₁⟩

section Split

variable {E : Type*} [NormedAddCommGroup E]

/-- For `p₀ ≤ p`, the part of `f` where `‖f‖` exceeds `‖f‖_p` has `L^{p₀}` norm at most
`‖f‖_p`. For `p = ∞` this part vanishes almost everywhere. -/
theorem eLpNorm_indicator_eLpNorm_lt_enorm_le {f : α → E} {p₀ p : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (h₀ : p₀ ≤ p) :
    eLpNorm ({x | eLpNorm f p μ < ‖f x‖ₑ}.indicator f) p₀ μ ≤ eLpNorm f p μ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · -- `‖f‖ ≤ ‖f‖_∞` almost everywhere, so the restriction vanishes almost everywhere.
    have h0 : {x | eLpNorm f ∞ μ < ‖f x‖ₑ}.indicator f =ᵐ[μ] 0 := by
      filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
      rw [← eLpNorm_exponent_top hf] at hx
      exact Set.indicator_of_notMem (not_lt.2 hx) f
    rw [eLpNorm_congr_ae h0, eLpNorm_zero]
    exact zero_le
  set t := eLpNorm f p μ
  set s := {x | t < ‖f x‖ₑ}
  have hs₀ : NullMeasurableSet s μ := nullMeasurableSet_lt aemeasurable_const hf.eNorm
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
  have hp₀ : 0 < p₀.toReal := ENNReal.toReal_pos hp₀0 (ne_top_of_le_ne_top hp h₀)
  refine eLpNorm_le_of_rpow_le_rpow_mul hp0 hp hp₀0 (ne_top_of_le_ne_top hp h₀) hf hs ht0 ht
    fun x => ?_
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    exact ENNReal.rpow_le_rpow_sub_mul_rpow hp₀ eNorm_ne_top
      (ENNReal.rpow_le_rpow_of_nonpos (le_of_lt hx) (sub_nonpos.2 (ENNReal.toReal_mono hp h₀)))
  · rw [Set.indicator_of_notMem hx, eNorm_zero, ENNReal.zero_rpow_of_pos hp₀]
    exact zero_le

/-- For `p ≤ p₁`, the part of `f` where `‖f‖` is at most `‖f‖_p` has `L^{p₁}` norm at most
`‖f‖_p`. -/
theorem eLpNorm_indicator_enorm_le_eLpNorm_le {f : α → E} {p p₁ : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (h₁ : p ≤ p₁) :
    eLpNorm ({x | ‖f x‖ₑ ≤ eLpNorm f p μ}.indicator f) p₁ μ ≤ eLpNorm f p μ := by
  set t := eLpNorm f p μ
  set s := {x | ‖f x‖ₑ ≤ t}
  have hs₀ : NullMeasurableSet s μ := nullMeasurableSet_le hf.eNorm aemeasurable_const
  have hs : AEStronglyMeasurable (s.indicator f) μ := hf.indicator₀ hs₀
  have hst (x : α) : ‖s.indicator f x‖ₑ ≤ t := by
    by_cases hx : x ∈ s
    · rw [Set.indicator_of_mem hx]
      exact hx
    · rw [Set.indicator_of_notMem hx, eNorm_zero]
      exact zero_le
  rcases eq_or_ne t 0 with ht0 | ht0
  · -- `s.indicator f` vanishes identically.
    have h0 : s.indicator f = 0 :=
      funext fun x => eNorm_eq_zero.1 (le_antisymm (ht0 ▸ hst x) bot_le)
    rw [h0, eLpNorm_zero, ht0]
  rcases eq_or_ne t ∞ with ht | ht
  · exact ht ▸ le_top
  have hp0 : p ≠ 0 := by
    rintro rfl
    exact ht0 (eLpNorm_exponent_zero hf)
  -- `s.indicator f` is bounded by `t` both in `Lᵖ` and pointwise.
  rw [← ENNReal.ofReal_toReal ht]
  refine eLpNorm_le_of_exponent_le hs hp0.bot_lt h₁ (ENNReal.toReal_pos ht0 ht)
    (by rw [ENNReal.ofReal_toReal ht]; exact eLpNorm_indicator_le f hs₀)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [← toReal_eNorm]
  exact ENNReal.toReal_mono ht (hst x)

/-- A function in `Lᵖ` is the sum of a function in `L^{p₀}` and a function in `L^{p₁}` for every
`p₀ ≤ p ≤ p₁`, each of norm at most `‖f‖_p`. This is the inclusion `Lᵖ ⊆ L^{p₀} + L^{p₁}`. -/
theorem MemLp.exists_add_ae_eq_of_le_of_le {f : α → E} {p₀ p p₁ : ℝ≥0∞} (hf : MemLp f p μ)
    (h₀ : p₀ ≤ p) (h₁ : p ≤ p₁) :
    ∃ g h : α → E, MemLp g p₀ μ ∧ eLpNorm g p₀ μ ≤ eLpNorm f p μ ∧
      MemLp h p₁ μ ∧ eLpNorm h p₁ μ ≤ eLpNorm f p μ ∧ g + h =ᵐ[μ] f := by
  -- Split `f` at the level `‖f‖_p`.
  have hf' := hf.aestronglyMeasurable
  have hg := eLpNorm_indicator_eLpNorm_lt_enorm_le hf' h₀
  have hh := eLpNorm_indicator_enorm_le_eLpNorm_le hf' h₁
  refine ⟨_, _, hg.trans_lt hf.eLpNorm_lt_top, hg, hh.trans_lt hf.eLpNorm_lt_top, hh,
    Filter.Eventually.of_forall fun x => ?_⟩
  by_cases hx : eLpNorm f p μ < ‖f x‖ₑ
  · simp [hx, not_le.2 hx]
  · simp [hx, not_lt.1 hx]

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

/-- **Logarithmic convexity of the `Lᵖ` norms.** If `0 ≤ θ ≤ 1` and
`1 / p = (1 - θ) / p₀ + θ / p₁`, then `‖f‖_p ≤ ‖f‖_{p₀} ^ (1 - θ) ‖f‖_{p₁} ^ θ`. -/
theorem eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow {f : α → ε} {p₀ p₁ p : ℝ≥0∞} {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) :
    eLpNorm f p μ ≤ eLpNorm f p₀ μ ^ (1 - θ) * eLpNorm f p₁ μ ^ θ := by
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · -- Every `eLpNorm` of `f` is infinite, and so is the right side.
    simp only [eLpNorm_of_not_aestronglyMeasurable hf]
    rcases hθ.1.eq_or_lt with rfl | hθ₀
    · simp
    · rw [ENNReal.top_rpow_of_pos hθ₀, ENNReal.mul_top]
      intro h
      rcases ENNReal.rpow_eq_zero_iff.1 h with ⟨h₁, -⟩ | ⟨-, h₂⟩
      · exact ENNReal.top_ne_zero h₁
      · linarith [hθ.2]
  rcases hθ.1.eq_or_lt with rfl | hθ₀
  · rw [sub_zero, ENNReal.ofReal_one, one_mul, ENNReal.ofReal_zero, zero_mul, add_zero,
      inv_inj] at hp
    simp [hp]
  rcases hθ.2.eq_or_lt with rfl | hθ₁
  · rw [sub_self, ENNReal.ofReal_zero, zero_mul, zero_add, ENNReal.ofReal_one, one_mul,
      inv_inj] at hp
    simp [hp]
  have ha : 0 < 1 - θ := sub_pos.2 hθ₁
  -- Hölder's inequality for `‖f‖ = ‖f‖ ^ (1 - θ) ‖f‖ ^ θ` with the exponents
  -- `p₀ / (1 - θ)` and `p₁ / θ`.
  have hr₀ : p₀ / ENNReal.ofReal (1 - θ) * ENNReal.ofReal (1 - θ) = p₀ :=
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 ha).ne' ENNReal.ofReal_ne_top
  have hr₁ : p₁ / ENNReal.ofReal θ * ENNReal.ofReal θ = p₁ :=
    ENNReal.div_mul_cancel (ENNReal.ofReal_pos.2 hθ₀).ne' ENNReal.ofReal_ne_top
  have : ENNReal.HolderTriple (p₀ / ENNReal.ofReal (1 - θ)) (p₁ / ENNReal.ofReal θ) p := by
    refine ⟨?_⟩
    rw [hp, ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)
      (Or.inl (ENNReal.ofReal_pos.2 ha).ne'), ENNReal.inv_div (Or.inl ENNReal.ofReal_ne_top)
      (Or.inl (ENNReal.ofReal_pos.2 hθ₀).ne'), div_eq_mul_inv, div_eq_mul_inv]
  calc eLpNorm f p μ = eLpNorm ((‖f ·‖ₑ ^ (1 - θ)) * (‖f ·‖ₑ ^ θ)) p μ := by
        rw [← eLpNorm_eNorm f hf]
        congr 1
        ext x
        rw [Pi.mul_apply, ← ENNReal.rpow_add_of_nonneg _ _ ha.le hθ₀.le, sub_add_cancel,
          ENNReal.rpow_one]
    _ ≤ eLpNorm (‖f ·‖ₑ ^ (1 - θ)) (p₀ / ENNReal.ofReal (1 - θ)) μ *
          eLpNorm (‖f ·‖ₑ ^ θ) (p₁ / ENNReal.ofReal θ) μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal (hf.eNorm.pow_const _).aestronglyMeasurable
          (hf.eNorm.pow_const _).aestronglyMeasurable
    _ = eLpNorm f p₀ μ ^ (1 - θ) * eLpNorm f p₁ μ ^ θ := by
        rw [eLpNorm_eNorm_rpow f hf ha, eLpNorm_eNorm_rpow f hf hθ₀, hr₀, hr₁]

/-- The `Lᵖ` norm at an intermediate exponent `p₀ ≤ p ≤ p₁`, with `p₀ ≠ 0`, is at most the
larger of the `L^{p₀}` and `L^{p₁}` norms: `‖f‖_p ≤ max (‖f‖_{p₀}, ‖f‖_{p₁})`. This is the
quantitative form of `MeasureTheory.MemLp.of_le_of_le`. -/
theorem eLpNorm_le_max_of_le_of_le {f : α → ε} {p₀ p p₁ : ℝ≥0∞} (hp₀ : p₀ ≠ 0) (h₀ : p₀ ≤ p)
    (h₁ : p ≤ p₁) : eLpNorm f p μ ≤ max (eLpNorm f p₀ μ) (eLpNorm f p₁ μ) := by
  rcases h₀.eq_or_lt with rfl | h₀'
  · exact le_max_left _ _
  -- Write `1 / p = (1 - θ) / p₀ + θ / p₁` and apply logarithmic convexity.
  have hp₀' : p₀⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hp₀
  have hp' : p⁻¹ ≠ ∞ := ne_top_of_le_ne_top hp₀' (ENNReal.inv_le_inv.2 h₀)
  have hp₁' : p₁⁻¹ ≠ ∞ := ne_top_of_le_ne_top hp' (ENNReal.inv_le_inv.2 h₁)
  have hle₁ : p₁⁻¹.toReal ≤ p⁻¹.toReal := ENNReal.toReal_mono hp' (ENNReal.inv_le_inv.2 h₁)
  have hlt₀ : p⁻¹.toReal < p₀⁻¹.toReal :=
    ENNReal.toReal_strict_mono hp₀' (ENNReal.inv_lt_inv.2 h₀')
  have hd : 0 < p₀⁻¹.toReal - p₁⁻¹.toReal := by linarith
  set θ := (p₀⁻¹.toReal - p⁻¹.toReal) / (p₀⁻¹.toReal - p₁⁻¹.toReal) with hθ_def
  have hθ : θ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg (by linarith) hd.le, div_le_one_of_le₀ (by linarith) hd.le⟩
  have hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹ := by
    rw [← ENNReal.ofReal_toReal hp', ← ENNReal.ofReal_toReal hp₀', ← ENNReal.ofReal_toReal hp₁',
      ← ENNReal.ofReal_mul (sub_nonneg.2 hθ.2), ← ENNReal.ofReal_mul hθ.1,
      ← ENNReal.ofReal_add (mul_nonneg (sub_nonneg.2 hθ.2) ENNReal.toReal_nonneg)
        (mul_nonneg hθ.1 ENNReal.toReal_nonneg)]
    congr 1
    rw [hθ_def]
    field_simp
    ring
  calc eLpNorm f p μ ≤ eLpNorm f p₀ μ ^ (1 - θ) * eLpNorm f p₁ μ ^ θ :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hθ hp
    _ ≤ max (eLpNorm f p₀ μ) (eLpNorm f p₁ μ) ^ (1 - θ) *
          max (eLpNorm f p₀ μ) (eLpNorm f p₁ μ) ^ θ := by
        gcongr
        · exact sub_nonneg.2 hθ.2
        · exact le_max_left _ _
        · exact le_max_right _ _
    _ = max (eLpNorm f p₀ μ) (eLpNorm f p₁ μ) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hθ.2) hθ.1, sub_add_cancel,
          ENNReal.rpow_one]

/-- **Logarithmic convexity of the `Lᵖ` norms**, for elements `f ∈ Lᵖ`, `f₀ ∈ L^{p₀}` and
`f₁ ∈ L^{p₁}` representing the same function: if `0 ≤ θ ≤ 1` and
`1 / p = (1 - θ) / p₀ + θ / p₁`, then `‖f‖ ≤ ‖f₀‖ ^ (1 - θ) ‖f₁‖ ^ θ`. -/
theorem Lp.norm_le_norm_rpow_mul_norm_rpow_of_ae_eq {E : Type*} [NormedAddCommGroup E]
    {p₀ p₁ p : ℝ≥0∞} {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hp : p⁻¹ = ENNReal.ofReal (1 - θ) * p₀⁻¹ + ENNReal.ofReal θ * p₁⁻¹) {f : Lp E p μ}
    {f₀ : Lp E p₀ μ} {f₁ : Lp E p₁ μ} (h₀ : (f : α → E) =ᵐ[μ] f₀) (h₁ : (f : α → E) =ᵐ[μ] f₁) :
    ‖f‖ ≤ ‖f₀‖ ^ (1 - θ) * ‖f₁‖ ^ θ := by
  have key : eLpNorm f p μ ≤ eLpNorm f₀ p₀ μ ^ (1 - θ) * eLpNorm f₁ p₁ μ ^ θ := by
    rw [← eLpNorm_congr_ae h₀, ← eLpNorm_congr_ae h₁]
    exact eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hθ hp
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, ENNReal.toReal_rpow, ENNReal.toReal_rpow,
    ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hθ.2) (Lp.eLpNorm_ne_top f₀))
    (ENNReal.rpow_ne_top_of_nonneg hθ.1 (Lp.eLpNorm_ne_top f₁))) key

end MeasureTheory
