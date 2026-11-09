/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

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
        rw [← eLpNorm_enorm f hf]
        congr 1
        ext x
        rw [Pi.mul_apply, ← ENNReal.rpow_add_of_nonneg _ _ ha.le hθ₀.le, sub_add_cancel,
          ENNReal.rpow_one]
    _ ≤ eLpNorm (‖f ·‖ₑ ^ (1 - θ)) (p₀ / ENNReal.ofReal (1 - θ)) μ *
          eLpNorm (‖f ·‖ₑ ^ θ) (p₁ / ENNReal.ofReal θ) μ :=
        eLpNorm_le_eLpNorm_mul_eLpNorm_ennreal (hf.enorm.pow_const _).aestronglyMeasurable
          (hf.enorm.pow_const _).aestronglyMeasurable
    _ = eLpNorm f p₀ μ ^ (1 - θ) * eLpNorm f p₁ μ ^ θ := by
        rw [eLpNorm_enorm_rpow f hf ha, eLpNorm_enorm_rpow f hf hθ₀, hr₀, hr₁]

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
