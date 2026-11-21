/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Statistics.Experiments.Risk
public import Mathlib.Probability.Decision.BayesEstimator
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Decision.Risk.Basic

/-!
# Admissible, Bayes, and minimax rules

Decision criteria are stated for a class of rules equipped with real risk functions. This
allows the same criteria to be used for deterministic and randomized procedures.
Admissibility concerns pointwise domination, Bayes optimality concerns integrated risk, and
minimax optimality concerns worst-case risk.

## References

* T. S. Ferguson, *Mathematical Statistics: A Decision Theoretic Approach*, Academic Press
  (1967), §§1.6, 2.1, 2.3, 2.11.
* J. O. Berger, *Statistical Decision Theory and Bayesian Analysis*, 2nd ed., Springer
  (1985), Theorems 8, 9, and 17.
-/

public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

variable {D Θ : Type*} {R : D → Θ → ℝ} {δ : D}

/-- A rule is admissible if no rule improves its risk at one parameter without increasing it
at another. -/
def IsAdmissibleRisk (R : D → Θ → ℝ) (δ : D) : Prop :=
  ∀ δ', R δ' ≤ R δ → R δ' = R δ

/-- A rule that is everywhere at least as good as an admissible rule has the same risk. -/
theorem IsAdmissibleRisk.eq_of_le (h : IsAdmissibleRisk R δ) {δ' : D}
    (hle : R δ' ≤ R δ) : R δ' = R δ :=
  h δ' hle

/-- Admissibility rules out domination with strict improvement at any parameter. -/
theorem isAdmissibleRisk_iff :
    IsAdmissibleRisk R δ ↔ ¬ ∃ δ', R δ' ≤ R δ ∧ ∃ θ, R δ' θ < R δ θ := by
  constructor
  · intro h ⟨δ', hle, θ, hlt⟩
    exact hlt.ne (congrFun (h δ' hle) θ)
  · intro h δ' hle
    exact funext fun θ ↦ (hle θ).antisymm (le_of_not_gt fun hlt ↦ h ⟨δ', hle, θ, hlt⟩)

/-- A Bayes rule has integrable risk and minimizes prior average risk among rules of
integrable risk. -/
structure IsBayesRule [MeasurableSpace Θ] (R : D → Θ → ℝ) (π : Measure Θ) (δ : D) : Prop where
  /-- The risk of the Bayes rule is integrable. -/
  integrable : Integrable (R δ) π
  /-- The Bayes rule minimizes the average risk. -/
  integral_le : ∀ δ', Integrable (R δ') π → ∫ θ, R δ θ ∂π ≤ ∫ θ, R δ' θ ∂π

/-- A minimax rule has bounded-above risk and minimizes worst-case risk among rules whose
risk is bounded above. -/
structure IsMinimaxRule (R : D → Θ → ℝ) (δ : D) : Prop where
  /-- The risk of the minimax rule is bounded above. -/
  bddAbove : BddAbove (range (R δ))
  /-- The minimax rule minimizes the supremum of risk. -/
  iSup_le : ∀ δ', BddAbove (range (R δ')) → ⨆ θ, R δ θ ≤ ⨆ θ, R δ' θ

section Bayes

variable [MeasurableSpace Θ] {π : Measure Θ}

/-- A Bayes rule is admissible if all rules with no greater pointwise risk are integrable and
Bayes rules are unique up to their risk functions. -/
theorem IsBayesRule.isAdmissibleRisk_of_unique (hδ : IsBayesRule R π δ)
    (hint : ∀ δ', R δ' ≤ R δ → Integrable (R δ') π)
    (huniq : ∀ δ', IsBayesRule R π δ' → R δ' = R δ) : IsAdmissibleRisk R δ := by
  intro δ' hle
  refine huniq δ' ⟨hint δ' hle, fun δ'' hδ'' ↦ ?_⟩
  exact (integral_mono (hint δ' hle) hδ.integrable hle).trans (hδ.integral_le δ'' hδ'')

/-- A Bayes rule with continuous risk is admissible for a prior charging every nonempty open set
if every dominating rule also has integrable, continuous risk. -/
theorem IsBayesRule.isAdmissibleRisk_of_continuous [TopologicalSpace Θ]
    [π.IsOpenPosMeasure] (hδ : IsBayesRule R π δ) (hc : Continuous (R δ))
    (hdom : ∀ δ', R δ' ≤ R δ → Integrable (R δ') π ∧ Continuous (R δ')) :
    IsAdmissibleRisk R δ := by
  rw [isAdmissibleRisk_iff]
  rintro ⟨δ', hle, θ, hlt⟩
  obtain ⟨hint, hc'⟩ := hdom δ' hle
  have hs : 0 < π (Function.support fun t ↦ R δ t - R δ' t) := by
    exact (isOpen_ne_fun (hc.sub hc') continuous_const).measure_pos π
      ⟨θ, sub_ne_zero.mpr hlt.ne'⟩
  have hpos := (integral_pos_iff_support_of_nonneg (fun t ↦ sub_nonneg.mpr (hle t))
    (hδ.integrable.sub hint)).2 hs
  rw [integral_sub hδ.integrable hint] at hpos
  exact (not_lt_of_ge (hδ.integral_le δ' hint)) (sub_pos.mp hpos)

/-- If a Bayes rule's average risk under a probability prior is an upper bound on all its risks,
the rule is minimax. That average risk also bounds the Bayes risk under every probability prior
for which the rule has integrable risk. -/
theorem IsMinimaxRule.of_isBayesRule_of_risk_le [IsProbabilityMeasure π]
    (hδ : IsBayesRule R π δ)
    (hint : ∀ δ', BddAbove (range (R δ')) → Integrable (R δ') π)
    (hle : ∀ θ, R δ θ ≤ ∫ t, R δ t ∂π) :
    IsMinimaxRule R δ ∧ ∀ (π' : Measure Θ) [IsProbabilityMeasure π'],
      Integrable (R δ) π' → ∀ δ', IsBayesRule R π' δ' →
        ∫ θ, R δ' θ ∂π' ≤ ∫ θ, R δ θ ∂π := by
  have havg {ν : Measure Θ} [IsProbabilityMeasure ν] {r : Θ → ℝ} (hr : Integrable r ν)
      {c : ℝ} (h : ∀ θ, r θ ≤ c) : ∫ θ, r θ ∂ν ≤ c := by
    simpa using integral_mono hr (integrable_const c) h
  constructor
  · refine ⟨⟨_, forall_mem_range.mpr hle⟩, fun δ' hb ↦ ?_⟩
    have : Nonempty Θ := nonempty_of_isProbabilityMeasure π
    exact (ciSup_le hle).trans <| (hδ.integral_le δ' (hint δ' hb)).trans <|
      havg (hint δ' hb) (le_ciSup hb)
  · intro π' _ hδ' δ' hBayes
    exact (hBayes.integral_le δ hδ').trans (havg hδ' hle)

end Bayes

section Kernel

variable {X A : Type*} [MeasurableSpace Θ] [MeasurableSpace X] [MeasurableSpace A]
  {L : Θ → A → ℝ} {π : Measure Θ}

/-- For a bounded measurable nonnegative loss, minimizing the prior average of real risks
over Markov rules is equivalent to attaining Mathlib's Bayes risk. -/
theorem isBayesRule_risk_iff_isBayesEstimator (P : Kernel Θ X) [IsMarkovKernel P]
    [IsFiniteMeasure π] (δ : {κ : Kernel X A // IsMarkovKernel κ})
    (hm : Measurable (Function.uncurry L)) (h₀ : ∀ θ a, 0 ≤ L θ a)
    {C : ℝ} (hC : ∀ θ a, L θ a ≤ C) :
    IsBayesRule (fun κ : {κ : Kernel X A // IsMarkovKernel κ} ↦ risk P L κ.val) π δ ↔
      IsBayesEstimator (fun θ a ↦ ENNReal.ofReal (L θ a)) P δ.val π := by
  let ℓ (θ : Θ) (a : A) := ENNReal.ofReal (L θ a)
  have hbound θ a : |L θ a| ≤ C := by rw [abs_of_nonneg (h₀ θ a)]; exact hC θ a
  have hint (κ : Kernel X A) [IsMarkovKernel κ] : Integrable (risk P L κ) π :=
    Integrable.of_bound (measurable_risk P hm).aestronglyMeasurable C <|
      ae_of_all _ fun θ ↦ by
        simpa only [Real.norm_eq_abs] using abs_risk_le (ae_of_all _ (hbound θ))
  have hnonneg (κ : Kernel X A) : 0 ≤ ∫ θ, risk P L κ θ ∂π :=
    integral_nonneg fun θ ↦ by
      rw [risk_def]
      exact integral_nonneg (h₀ θ)
  have hconvert (κ : Kernel X A) [IsMarkovKernel κ] :
      ENNReal.ofReal (∫ θ, risk P L κ θ ∂π) = avgRisk ℓ P κ π := by
    apply ofReal_integral_risk_eq_avgRisk P π (hint κ)
    exact ae_of_all _ fun θ ↦
      ⟨Integrable.of_bound (hm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable C
        (ae_of_all _ fun a ↦ by simpa only [Real.norm_eq_abs] using hbound θ a),
       ae_of_all _ (h₀ θ)⟩
  let := δ.property
  constructor
  · intro h
    apply le_antisymm _ (bayesRisk_le_avgRisk ℓ P δ.val π)
    apply le_iInf₂
    intro κ hκ
    rw [← hconvert δ.val, ← hconvert κ]
    exact ENNReal.ofReal_le_ofReal (h.integral_le ⟨κ, hκ⟩ (hint κ))
  · intro h
    refine ⟨hint δ.val, fun ⟨κ, hκ⟩ _ ↦ ?_⟩
    apply (ENNReal.ofReal_le_ofReal_iff (hnonneg κ)).mp
    rw [hconvert δ.val, hconvert κ, h]
    exact bayesRisk_le_avgRisk ℓ P κ π

end Kernel

end TauCeti
