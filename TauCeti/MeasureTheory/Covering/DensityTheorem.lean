/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.DensityTheorem
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
-- Proof-only: open and closed balls agree up to a null set for an additive Haar measure.
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Lebesgue points along concentric closed balls

Mathlib's `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub` states the Lebesgue
differentiation theorem for a uniformly locally doubling measure along arbitrary families of
closed balls shrinking to a point. This file records its most common special case: almost every
point `x` is a Lebesgue point of a locally integrable function `f` in the sense that the mean
oscillation `⨍_{closedBall x r} ‖f - f x‖` tends to zero as `r → 0⁺`, and the analogous statement
for the averages of an integrable `ℝ≥0∞`-valued function. For an additive Haar measure on a
finite-dimensional real normed space, spheres are null, so the same averages over open balls
converge as well.
-/

public section

open Filter Metric MeasureTheory
open scoped ENNReal Topology

namespace IsUnifLocDoublingMeasure

variable {α E : Type*} [PseudoMetricSpace α] [MeasurableSpace α] (μ : Measure α)
  [IsUnifLocDoublingMeasure μ] [SecondCountableTopology α] [BorelSpace α]
  [IsLocallyFiniteMeasure μ] [NormedAddCommGroup E]

/-- **Lebesgue differentiation theorem along concentric closed balls.** For a uniformly locally
doubling measure, almost every point `x` is a Lebesgue point of a locally integrable function `f`:
the mean oscillation `⨍_{closedBall x r} ‖f - f x‖` tends to zero as `r → 0⁺`. -/
theorem ae_tendsto_average_closedBall_norm_sub {f : α → E} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍ y in closedBall x r, ‖f y - f x‖ ∂μ) (𝓝[>] 0) (𝓝 0) := by
  filter_upwards [ae_tendsto_average_norm_sub μ hf 1] with x hx
  exact hx (fun _ => x) id tendsto_id (eventually_mem_nhdsWithin.mono fun r hr =>
    mem_closedBall_self (by simpa using (le_of_lt hr)))

/-- **Lebesgue differentiation theorem along concentric closed balls, for `ℝ≥0∞`-valued
functions.** For a uniformly locally doubling measure and an a.e. measurable `f` with finite
integral, the averages `⨍_{closedBall x r} f` tend to `f x` as `r → 0⁺` for almost every `x`. -/
theorem ae_tendsto_setLAverage_closedBall {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hfin : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍⁻ y in closedBall x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [(vitaliFamily μ 1).ae_tendsto_lintegral_div hf hfin] with x hx
  refine (hx.comp (tendsto_closedBall_filterAt μ (fun _ => x) id tendsto_id
    (eventually_mem_nhdsWithin.mono fun r hr =>
      mem_closedBall_self (by simpa using (le_of_lt hr))))).congr fun r => ?_
  simp only [Function.comp_apply, id, setLAverage_eq]

end IsUnifLocDoublingMeasure

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **Lebesgue differentiation theorem along concentric open balls, for an additive Haar
measure.** For an a.e. measurable `f : E → ℝ≥0∞` with finite integral, the averages
`⨍_{ball x r} f` tend to `f x` as `r → 0⁺` for almost every `x`. Open and closed balls of positive
radius differ by a null set, so this is `IsUnifLocDoublingMeasure.ae_tendsto_setLAverage_closedBall`
for open balls. -/
theorem ae_tendsto_setLAverage_ball (μ : Measure E) [μ.IsAddHaarMeasure] {f : E → ℝ≥0∞}
    (hf : AEMeasurable f μ) (hfin : ∫⁻ x, f x ∂μ ≠ ∞) :
    ∀ᵐ x ∂μ, Tendsto (fun r => ⨍⁻ y in ball x r, f y ∂μ) (𝓝[>] 0) (𝓝 (f x)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_setLAverage_closedBall μ hf hfin] with x hx
  refine Tendsto.congr' ?_ hx
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact setLAverage_congr (μ.addHaar_closedBall_ae_eq_ball_of_ne_zero x r (ne_of_gt hr))

end MeasureTheory.Measure
