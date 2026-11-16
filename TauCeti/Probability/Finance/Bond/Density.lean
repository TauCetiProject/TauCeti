/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Bond.Basic
public import TauCeti.Probability.Finance.SimpleStrategy.L1Approximation

/-!
# Predictable approximation in absolute bond variation

The absolute variation of the money-market account has density `|r β|`. Every predictable
holding integrable for the expected absolute-variation measure admits approximation in that
measure's L¹ norm by bounded finite-grid holdings, chosen at the left endpoints. Thus the
approximations preserve the information constraint of trading and control precisely the
absolute-income error, even when the rate vanishes or changes sign.

The weight is the absolute-variation density identified by
`variation_vectorMeasureIcc_bondPrice` in `TauCeti.Probability.Finance.Bond.Trading`, and
`Filtration.exists_seq_simpleHolding_tendsto_eLpNorm_one_of_isStronglyPredictable` supplies
the density theorem. The hypothesis is expected absolute-variation integrability; no square
moment, path continuity or boundedness of the holding is assumed. The result constructs
approximations, and does not assert a self-financing identity or a stochastic stock integral.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter TauCeti.Probability
open scoped ENNReal NNReal Topology

namespace TauCeti.Finance

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {ℱ : Filtration ℝ≥0 mΩ} {r : ℝ → ℝ} {β₀ : ℝ} {T : ℝ≥0}

/-- A predictable bond holding with finite expected absolute interest income can be
approximated in expected absolute-variation L¹ by bounded left-measurable finite-grid
holdings. Only continuity of the rate on the declared horizon is required. Rates and
holdings may have either sign, and neither the initial bond price nor the horizon needs
to be positive. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_one_bondPrice
    (hr : ContinuousOn r (Icc 0 (T : ℝ)))
    {b : ℝ≥0 → Ω → ℝ} (hb : IsStronglyPredictable ℱ b)
    (hint : Integrable (Function.uncurry b)
      (((timeMeasure T).prod P).withDensity
        (fun p : ℝ≥0 × Ω ↦ ‖r p.1 * bondPrice r β₀ p.1‖ₑ))) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      Tendsto (fun k ↦ eLpNorm
        (fun p ↦ simpleHolding (τ k) (n k) (a k) p.1 p.2 - b p.1 p.2) 1
        (((timeMeasure T).prod P).withDensity
          (fun p : ℝ≥0 × Ω ↦ ‖r p.1 * bondPrice r β₀ p.1‖ₑ))) atTop (𝓝 0) := by
  have hcont : ContinuousOn (fun u : ℝ≥0 ↦ r u * bondPrice r β₀ u) (Icc 0 T) :=
    (hr.mul (continuousOn_bondPrice hr β₀)).comp (by fun_prop)
      (fun u hu ↦ ⟨by exact_mod_cast hu.1, by exact_mod_cast hu.2⟩)
  have htime : Integrable (fun u : ℝ≥0 ↦ r u * bondPrice r β₀ u) (timeMeasure T) := by
    rw [timeMeasure_def]
    apply hcont.integrableOn_of_subset_isCompact isCompact_Icc measurableSet_Ioc
      Ioc_subset_Icc_self
    simpa only [timeMeasure_def, Measure.restrict_apply_univ] using
      (measure_ne_top (timeMeasure T) univ)
  have : IsFiniteMeasure (((timeMeasure T).prod P).withDensity
      (fun p : ℝ≥0 × Ω ↦ ‖r p.1 * bondPrice r β₀ p.1‖ₑ)) :=
    isFiniteMeasure_withDensity (htime.comp_fst P).hasFiniteIntegral.ne
  exact ℱ.exists_seq_simpleHolding_tendsto_eLpNorm_one_of_isStronglyPredictable _
    (withDensity_absolutelyContinuous _ _
      (by simp only [Measure.prod_prod, timeMeasure_singleton_zero, zero_mul])) hb hint

end TauCeti.Finance
