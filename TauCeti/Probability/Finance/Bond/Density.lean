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

/-- The bond's interest-income density is integrable on the finite horizon `[0, T]`
when the short rate is continuous there. -/
theorem integrable_mul_bondPrice_timeMeasure (hr : ContinuousOn r (Icc 0 (T : ℝ))) :
    Integrable (fun t : ℝ≥0 ↦ r t * bondPrice r β₀ t) (timeMeasure T) := by
  have hc : ContinuousOn (fun t : ℝ≥0 ↦ r t * bondPrice r β₀ t) (Icc 0 T) :=
    (hr.mul (continuousOn_bondPrice hr β₀)).comp NNReal.continuous_coe.continuousOn
      (fun t ht ↦ ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩)
  have h := (hc.integrableOn_Icc (μ := timeMeasure T)).mono_set Ioc_subset_Icc_self
  simpa only [IntegrableOn, timeMeasure_restrict, min_self] using h

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
  have hi := integrable_mul_bondPrice_timeMeasure (β₀ := β₀) hr
  have hw := hi.aestronglyMeasurable.comp_fst (ν := P)
  let ν := (timeMeasure T).withDensity
    (fun t : ℝ≥0 ↦ ‖r t * bondPrice r β₀ t‖ₑ)
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity (hasFiniteIntegral_iff_eNorm.mp hi.hasFiniteIntegral).ne
  have hν : ν {0} = 0 :=
    (withDensity_absolutelyContinuous _ _) (timeMeasure_singleton_zero T)
  have hbν : Integrable (Function.uncurry b) (ν.prod P) := by
    refine ⟨(hb.mono ℱ.predictable_le_prod).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm, prod_withDensity_left₀ hi.aestronglyMeasurable.eNorm,
      lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hw.eNorm
        (ae_of_all _ fun _ ↦ eNorm_lt_top)]
    simpa only [hasFiniteIntegral_iff_eNorm, Pi.mul_apply, Function.uncurry_def,
      eNorm_mul, mul_comm] using hb₁.hasFiniteIntegral
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hbound, hmean, hpath⟩ :=
    ℱ.exists_seq_simpleHolding_tendsto_eLpNorm_one_and_ae_tendsto_lintegral ν hν P hb hbν
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hbound, hmean.congr fun m ↦ ?_, ?_⟩
  · have he : StronglyMeasurable
        (fun p : ℝ≥0 × Ω ↦ simpleHolding (τ m) (n m) (a m) p.1 p.2 - b p.1 p.2) := by
      simpa only [Pi.sub_def, Function.uncurry_def] using
        ((isStronglyPredictable_simpleHolding (ha m)).sub hb).mono ℱ.predictable_le_prod
    have hew : AEStronglyMeasurable (fun p : ℝ≥0 × Ω ↦
        (simpleHolding (τ m) (n m) (a m) p.1 p.2 - b p.1 p.2) *
          (r p.1 * bondPrice r β₀ p.1)) ((timeMeasure T).prod P) := by
      simpa only [Pi.mul_def] using he.aestronglyMeasurable.mul hw
    rw [eLpNorm_one_eq_lintegral_eNorm he.aestronglyMeasurable,
      eLpNorm_one_eq_lintegral_eNorm hew,
      prod_withDensity_left₀ hi.aestronglyMeasurable.eNorm,
      lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ hw.eNorm
        (ae_of_all _ fun _ ↦ eNorm_lt_top)]
    simp only [Pi.mul_apply, eNorm_mul, mul_comm]
  · simpa only [ν, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
      hi.aestronglyMeasurable.eNorm (ae_of_all _ fun _ ↦ eNorm_lt_top), Pi.mul_apply]
      using hpath

end TauCeti.Finance
