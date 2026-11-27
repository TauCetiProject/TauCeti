/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Prod
import TauCeti.InformationTheory.KullbackLeibler.Variational

/-!
# The PAC-Bayesian change of measure inequality

An exponential moment bound for each fixed hypothesis gives one exceptional set of samples
outside which an integral bound holds simultaneously for every posterior of finite relative
entropy. The exceptional set is controlled by the exponential moment averaged over the prior.
This allows the posterior to be chosen after observing the sample.

The argument combines Markov's inequality with the Donsker–Varadhan inequality
`TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`. See P. Alquier,
*User-friendly introduction to PAC-Bayes bounds*, Lemma 2.2 and proof of Theorem 2.1,
and O. Catoni, *PAC-Bayesian supervised classification*, Theorem 1.1.4.
-/

public section

open MeasureTheory InformationTheory
open Real (exp log)
open scoped ENNReal

namespace TauCeti

/-- If `π`-almost every hypothesis has exponential moment at most one under the sample law `μ`, the
samples on which some posterior violates the change of measure bound have outer probability
at most `δ`. The prior `π` is fixed and the posterior ranges over all probability measures
of finite relative entropy to `π`. -/
theorem measure_exists_integral_gt_klDiv_add_log_le {Θ Ω : Type*}
    [MeasurableSpace Θ] [MeasurableSpace Ω] (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (π : Measure Θ) [IsProbabilityMeasure π] {f : Θ → Ω → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hmoment : ∀ᵐ θ ∂π, ∫⁻ ω, ENNReal.ofReal (exp (f θ ω)) ∂μ ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    μ {ω | ∃ ρ : Measure Θ, IsProbabilityMeasure ρ ∧ klDiv ρ π ≠ ∞ ∧
      (klDiv ρ π).toReal + log (1 / δ) < ∫ θ, f θ ω ∂ρ} ≤ ENNReal.ofReal δ := by
  rcases le_or_gt 1 δ with hlarge | hsmall
  · exact prob_le_one.trans (by simpa using ENNReal.ofReal_le_ofReal hlarge)
  let F (ω : Ω) := ∫⁻ θ, ENNReal.ofReal (exp (f θ ω)) ∂π
  have hmeas : Measurable (Function.uncurry fun θ ω ↦ ENNReal.ofReal (exp (f θ ω))) :=
    hf.exp.ennreal_ofReal
  have hmean : ∫⁻ ω, F ω ∂μ ≤ 1 := calc
    _ = ∫⁻ θ, ∫⁻ ω, ENNReal.ofReal (exp (f θ ω)) ∂μ ∂π :=
      (lintegral_lintegral_swap hmeas.aemeasurable).symm
    _ ≤ ∫⁻ _ : Θ, 1 ∂π := lintegral_mono_ae hmoment
    _ = 1 := by simp
  have hpos : 0 < 1 / δ := one_div_pos.mpr hδ
  refine (measure_mono (t := {ω | ENNReal.ofReal (1 / δ) ≤ F ω}) ?_).trans ?_
  · rintro ω ⟨ρ, hρ, hKL, hbad⟩
    simp only [Set.mem_ofPred_eq]
    by_contra! hsmallF
    have hnonneg := ae_of_all π fun θ ↦ (Real.exp_pos (f θ ω)).le
    have hexp : Integrable (fun θ ↦ exp (f θ ω)) π :=
      (lintegral_ofReal_ne_top_iff_integrable hf.of_uncurry_right.exp.aestronglyMeasurable
        hnonneg).mp (hsmallF.trans ENNReal.ofReal_lt_top).ne
    have hZ : (∫ θ, exp (f θ ω) ∂π) < 1 / δ := by
      apply (ENNReal.ofReal_lt_ofReal_iff hpos).mp
      rwa [ofReal_integral_eq_lintegral_ofReal hexp hnonneg]
    by_cases hint : Integrable (fun θ ↦ f θ ω) ρ
    · have hDV := (ENNReal.ofReal_le_iff_le_toReal hKL).mp
        (ofReal_integral_sub_log_integral_exp_le_klDiv hint hexp)
      linarith [Real.log_le_log (integral_exp_pos hexp) hZ.le]
    · rw [integral_undef hint] at hbad
      have hlog := Real.log_nonneg (one_le_one_div hδ hsmall.le)
      exact (add_nonneg ENNReal.toReal_nonneg hlog).not_gt hbad
  · calc
      _ ≤ (∫⁻ ω, F ω ∂μ) / ENNReal.ofReal (1 / δ) :=
        meas_ge_le_lintegral_div hmeas.lintegral_prod_left.aemeasurable
          (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top
      _ ≤ 1 / ENNReal.ofReal (1 / δ) := by gcongr
      _ = _ := by simp [one_div, ENNReal.ofReal_inv_of_pos hδ]

end TauCeti
