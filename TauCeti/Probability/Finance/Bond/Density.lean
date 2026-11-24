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

On a finite horizon with continuous short rate and finite sample measure, one sequence
also converges almost surely in pathwise absolute-variation L¹. This simultaneous
convergence is provided by
`exists_seq_simpleHolding_tendsto_eLpNorm_one_and_ae_tendsto_lintegral_bondPrice`.

The weight is the absolute-variation density identified by
`variation_vectorMeasureIcc_bondPrice` in `TauCeti.Probability.Finance.Bond.Trading`, and
`Filtration.exists_seq_simpleHolding_tendsto_eLpNorm_one_and_ae_tendsto_lintegral` supplies
the simultaneous approximation theorem. The hypothesis is expected absolute-variation
integrability; no square moment, path continuity or boundedness of the holding is assumed.
The result constructs approximations, and does not assert a self-financing identity or a
stochastic stock integral.

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

/-- On the finite horizon `[0, T]`, with continuous short rate `r` and finite sample measure
`P`, bounded finite-grid bond holdings approximate every predictable holding with finite
expected absolute interest income. Convergence holds in expected absolute bond variation
and almost surely in pathwise absolute bond variation, for the same sequence. Trading
heights are measurable at the left endpoints. Zero rates and a zero horizon are allowed. -/
theorem exists_seq_simpleHolding_tendsto_eLpNorm_one_and_ae_tendsto_lintegral_bondPrice
    (hr : ContinuousOn r (Icc 0 (T : ℝ)))
    {b : ℝ≥0 → Ω → ℝ} (hb : IsStronglyPredictable ℱ b)
    (hb₁ : Integrable (fun p : ℝ≥0 × Ω ↦ b p.1 p.2 * (r p.1 * bondPrice r β₀ p.1))
      ((timeMeasure T).prod P)) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ m, τ m 0 = 0) ∧ (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      Tendsto (fun m ↦ eLpNorm
        (fun p ↦ (simpleHolding (τ m) (n m) (a m) p.1 p.2 - b p.1 p.2) *
          (r p.1 * bondPrice r β₀ p.1)) 1 ((timeMeasure T).prod P)) atTop (𝓝 0) ∧
      ∀ᵐ ω ∂P, Tendsto (fun m ↦ ∫⁻ t : ℝ≥0,
        ‖r t * bondPrice r β₀ t‖ₑ *
          ‖simpleHolding (τ m) (n m) (a m) t ω - b t ω‖ₑ
            ∂timeMeasure T) atTop (𝓝 0) := by
  exact ℱ.exists_seq_simpleHolding_tendsto_eLpNorm_one_and_ae_tendsto_lintegral
    (timeMeasure T) (timeMeasure_singleton_zero T) P
    ((integrable_mul_bondPrice_timeMeasure hr β₀).comp_fst P) hb hb₁

end TauCeti.Finance
