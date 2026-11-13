/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Bond.Trading
public import TauCeti.Probability.Finance.SimpleStrategy.Approximation

/-!
# Finite-grid approximation in absolute bond variation

A predictable bond holding with finite expected absolute interest income admits bounded,
left-measurable finite-grid approximations in expected bond-variation L¹. The same sequence
converges almost surely in pathwise bond-variation L¹. This supplies actual elementary
holdings for passing from finite trading gains to the pathwise bond integral.

The time weight is `|r(t) β(t)|`, the density identified by
`variation_vectorMeasureIcc_bondPrice`. It may vanish on entire intervals. Neither the
holding nor its square needs to be integrable for unweighted time-product measure.
The expected absolute-income hypothesis is explicit; the theorem does not assert that
arbitrary pathwise integrable holdings have finite expected income. Rates, positions and
the initial bond value may have either sign. No Brownian motion or path regularity of
holdings is required.

Time is nonnegative real time, and rates and bond prices are evaluated by coercion to real
time. Approximation uses the existing predictable-rectangle density and the almost-sure
subsequence principle for nonnegative integrals.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2.
-/

public noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Finance

/-- Bounded finite-grid bond holdings approximate every predictable holding with finite
expected absolute interest income. Convergence holds in expected absolute bond variation
and almost surely in pathwise absolute bond variation, for the same sequence. Trading
heights are measurable at the left endpoints. Zero rates and a zero horizon are allowed. -/
theorem exists_seq_simpleHolding_tendsto_bondVariation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
    {P : Measure Ω} [IsFiniteMeasure P] {r : ℝ → ℝ} {T : ℝ≥0}
    (hr : ContinuousOn r (Icc 0 (T : ℝ))) (β₀ : ℝ)
    {b : ℝ≥0 → Ω → ℝ} (hb : IsStronglyPredictable ℱ b)
    (hb₁ : MemLp (Function.uncurry b) 1
      (((Probability.timeMeasure T).withDensity
        (fun t : ℝ≥0 ↦ ‖r t * bondPrice r β₀ t‖ₑ)).prod P)) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ m, τ m 0 = 0) ∧ (∀ m, StrictMonoOn (τ m) (Iic (n m))) ∧
      (∀ m j, j < n m → StronglyMeasurable[ℱ (τ m j)] (a m j)) ∧
      (∀ m j, j < n m → ∀ ω, ‖a m j ω‖ ≤ C m) ∧
      Tendsto (fun m ↦ eLpNorm
        (fun p ↦ simpleHolding (τ m) (n m) (a m) p.1 p.2 - b p.1 p.2) 1
        (((Probability.timeMeasure T).withDensity
          (fun t : ℝ≥0 ↦ ‖r t * bondPrice r β₀ t‖ₑ)).prod P)) atTop (𝓝 0) ∧
      ∀ᵐ ω ∂P, Tendsto (fun m ↦ ∫⁻ t : ℝ≥0,
        ‖r t * bondPrice r β₀ t‖ₑ *
          ‖simpleHolding (τ m) (n m) (a m) t ω - b t ω‖ₑ
            ∂Probability.timeMeasure T) atTop (𝓝 0) := by
  have hc : ContinuousOn (fun t : ℝ≥0 ↦ r t * bondPrice r β₀ t) (Icc 0 T) :=
    (hr.mul (continuousOn_bondPrice hr β₀)).comp NNReal.continuous_coe.continuousOn
      (fun t ht ↦ ⟨t.coe_nonneg, by exact_mod_cast ht.2⟩)
  have hi : Integrable (fun t : ℝ≥0 ↦ r t * bondPrice r β₀ t)
      (Probability.timeMeasure T) := by
    have h := (hc.integrableOn_Icc (μ := Probability.timeMeasure T)).mono_set
      Ioc_subset_Icc_self
    simpa only [IntegrableOn, Probability.timeMeasure_restrict, min_self] using h
  let ν := (Probability.timeMeasure T).withDensity
    (fun t : ℝ≥0 ↦ ‖r t * bondPrice r β₀ t‖ₑ)
  have : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity (hasFiniteIntegral_iff_eNorm.mp hi.hasFiniteIntegral).ne
  have hν : ν {0} = 0 :=
    (withDensity_absolutelyContinuous _ _)
      (Probability.timeMeasure_singleton_zero T)
  obtain ⟨n, τ, a, C, hτ₀, hτ, ha, hbound, hmean, hpath⟩ :=
    ℱ.exists_seq_simpleHolding_tendsto_eLpNorm_one_ae ν hν P hb hb₁
  refine ⟨n, τ, a, C, hτ₀, hτ, ha, hbound, hmean, ?_⟩
  simpa only [ν, lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _
    hi.aestronglyMeasurable.eNorm (ae_of_all _ fun _ ↦ eNorm_lt_top), Pi.mul_apply]
    using hpath

end TauCeti.Finance
