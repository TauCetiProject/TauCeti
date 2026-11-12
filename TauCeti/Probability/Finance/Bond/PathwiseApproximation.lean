/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Finance.Bond.Trading
public import TauCeti.Probability.Finance.SimpleStrategy.PathwiseApproximation

/-!
# Approximating pathwise-integrable bond holdings

Predictable bond holdings can be approximated almost surely in absolute-variation L¹ by
bounded finite-grid holdings. Only pathwise integrability is assumed: the absolute interest
income need not have finite expectation. The time coordinate is nonnegative, so the bond's
finite-horizon variation measure is pulled back along `ℝ≥0 → ℝ`.

By `variation_vectorMeasureIcc_bondPrice`, this is exactly the measure of absolute interest
income, with density `|r β|` on `(0,T]`. Signed rates, zero-rate intervals and the zero horizon
are allowed. The result constructs the approximating holdings; it does not assert
self-financing or convergence of stock gains.

## References

* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer,
  2004, §5.2.
-/

public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace TauCeti.Finance

/-- Bond-variation-integrable predictable holdings admit bounded, left-measurable finite-grid
approximations in almost-sure pathwise L¹. No moment bound on the holding or its absolute
interest income is required. All integrals use the bond's actual variation measure, in
nonnegative time coordinates. -/
theorem exists_seq_simpleHolding_ae_tendsto_bondVariation
    {Ω : Type*} {mΩ : MeasurableSpace Ω} (ℱ : Filtration ℝ≥0 mΩ)
    (P : Measure Ω) [IsFiniteMeasure P] {r : ℝ → ℝ} {T : ℝ}
    (hr : ContinuousOn r (Icc 0 T)) (hT : 0 ≤ T) (β₀ : ℝ)
    {b : ℝ≥0 → Ω → ℝ} (hb : IsStronglyPredictable ℱ b)
    (hint : ∀ᵐ ω ∂P, Integrable (fun t ↦ b t ω)
      (((boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT).variation.comap
        ((↑) : ℝ≥0 → ℝ))) :
    ∃ (n : ℕ → ℕ) (τ : ℕ → ℕ → ℝ≥0) (a : ℕ → ℕ → Ω → ℝ) (C : ℕ → ℝ),
      (∀ k, τ k 0 = 0) ∧ (∀ k, StrictMonoOn (τ k) (Iic (n k))) ∧
      (∀ k j, j < n k → StronglyMeasurable[ℱ (τ k j)] (a k j)) ∧
      (∀ k j, j < n k → ∀ ω, ‖a k j ω‖ ≤ C k) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k ↦ ∫⁻ t,
        ‖simpleHolding (τ k) (n k) (a k) t ω - b t ω‖ₑ
          ∂(((boundedVariationOn_bondPrice hr hT β₀).vectorMeasureIcc hT).variation.comap
            ((↑) : ℝ≥0 → ℝ))) atTop (𝓝 0) := by
  apply ℱ.exists_seq_simpleHolding_ae_tendsto_lintegral_enorm_sub _ P _ hb hint
  rw [NNReal.isClosedEmbedding_coe.measurableEmbedding.comap_apply,
    image_singleton, NNReal.coe_zero, variation_vectorMeasureIcc_bondPrice hr hT]
  exact measure_singleton 0

end TauCeti.Finance
