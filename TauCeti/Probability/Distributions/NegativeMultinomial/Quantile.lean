/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Quantile
public import TauCeti.Probability.Distributions.NegativeMultinomial.Aggregation

/-!
# Quantiles of negative-multinomial observables

Each coordinate and the total count of a negative-multinomial vector have negative-binomial
laws. Their real-cast lower quantiles are therefore identified with the corresponding scalar
negative-binomial quantiles, whose API supplies the cumulative-mass crossing characterization.

This file gives the coordinate and total quantile identifications, including the shape-zero
Dirac boundary, and their one-sided endpoint limits. A coordinate has unbounded upper support
exactly when the shape and its category weight are positive. The total has unbounded upper
support exactly when the shape is positive and the success weight is below one.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem map_cast_eval_negativeMultinomialMeasure (r p₀ : ℝ) (p : ι → ℝ≥0) (i : ι) :
    (negativeMultinomialMeasure r p₀ p).map (fun k ↦ (k i : ℝ)) =
      ((negativeMultinomialMeasure r p₀ p).map (fun k ↦ k i)).map
        (Nat.cast : ℕ → ℝ) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

private theorem map_cast_sum_negativeMultinomialMeasure (r p₀ : ℝ) (p : ι → ℝ≥0) :
    (negativeMultinomialMeasure r p₀ p).map (fun k ↦ ((∑ i, k i : ℕ) : ℝ)) =
      ((negativeMultinomialMeasure r p₀ p).map (fun k ↦ ∑ i, k i)).map
        (Nat.cast : ℕ → ℝ) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The real-cast quantile of a negative-multinomial coordinate is the quantile of its
negative-binomial marginal. This includes shape zero and zero category weights. -/
theorem quantile_map_cast_eval_negativeMultinomialMeasure {r p₀ : ℝ} (hr : 0 ≤ r)
    (hp₀ : 0 < p₀) {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1)
    (i : ι) (u : ℝ) :
    ((negativeMultinomialMeasure r p₀ p).map (fun x ↦ (x i : ℝ))).quantile u =
      ((negativeBinomialMeasure r (p₀ / (p₀ + p i))).map
        (Nat.cast : ℕ → ℝ)).quantile u := by
  rw [map_cast_eval_negativeMultinomialMeasure, map_eval_negativeMultinomialMeasure hr hp₀ hp i]

/-- The real-cast quantile of the total negative-multinomial count is the quantile of its
negative-binomial marginal. This includes empty category types and shape zero. -/
theorem quantile_map_cast_sum_negativeMultinomialMeasure {r p₀ : ℝ} (hr : 0 ≤ r)
    (hp₀ : 0 < p₀) {p : ι → ℝ≥0} (hp : p₀ + ∑ i, (p i : ℝ) = 1) (u : ℝ) :
    ((negativeMultinomialMeasure r p₀ p).map
      (fun x ↦ ((∑ i, x i : ℕ) : ℝ))).quantile u =
      ((negativeBinomialMeasure r p₀).map (Nat.cast : ℕ → ℝ)).quantile u := by
  rw [map_cast_sum_negativeMultinomialMeasure, map_sum_negativeMultinomialMeasure hr hp₀ hp]

/-- Every valid real-cast coordinate has lower support endpoint zero. -/
theorem tendsto_quantile_map_cast_eval_negativeMultinomialMeasure_nhdsGT_zero
    {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    Tendsto ((negativeMultinomialMeasure r p₀ p).map
      (fun x ↦ (x i : ℝ))).quantile (𝓝[>] 0) (𝓝 0) := by
  rw [map_cast_eval_negativeMultinomialMeasure, map_eval_negativeMultinomialMeasure hr hp₀ hp i]
  have hden : 0 < p₀ + (p i : ℝ) := by positivity
  exact tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsGT_zero hr
    (div_pos hp₀ hden) ((div_le_one hden).2 (le_add_of_nonneg_right (p i).coe_nonneg))

/-- The upper support endpoint of a valid real-cast coordinate is positive infinity exactly
when both the shape and that category's weight are positive. -/
theorem tendsto_quantile_map_cast_eval_negativeMultinomialMeasure_nhdsLT_one
    {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    Tendsto (fun u ↦ (((negativeMultinomialMeasure r p₀ p).map
      (fun x ↦ (x i : ℝ))).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if r = 0 ∨ p i = 0 then (0 : EReal) else ⊤)) := by
  rw [map_cast_eval_negativeMultinomialMeasure, map_eval_negativeMultinomialMeasure hr hp₀ hp i]
  have hden : 0 < p₀ + (p i : ℝ) := by positivity
  simpa only [div_eq_one_iff_eq hden.ne', left_eq_add, NNReal.coe_eq_zero] using
    tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsLT_one hr
      (div_pos hp₀ hden) ((div_le_one hden).2 (le_add_of_nonneg_right (p i).coe_nonneg))

/-- Every valid real-cast total count has lower support endpoint zero. -/
theorem tendsto_quantile_map_cast_sum_negativeMultinomialMeasure_nhdsGT_zero
    {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    Tendsto ((negativeMultinomialMeasure r p₀ p).map
      (fun x ↦ ((∑ i, x i : ℕ) : ℝ))).quantile (𝓝[>] 0) (𝓝 0) := by
  rw [map_cast_sum_negativeMultinomialMeasure, map_sum_negativeMultinomialMeasure hr hp₀ hp]
  have hp₀_le : p₀ ≤ 1 := calc
    p₀ ≤ p₀ + ∑ i, (p i : ℝ) :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ (p _).coe_nonneg)
    _ = 1 := hp
  exact tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsGT_zero hr hp₀
    hp₀_le

/-- The upper support endpoint of a valid real-cast total is positive infinity exactly away
from the shape-zero and success-weight-one Dirac boundaries. -/
theorem tendsto_quantile_map_cast_sum_negativeMultinomialMeasure_nhdsLT_one
    {r p₀ : ℝ} (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    Tendsto (fun u ↦ (((negativeMultinomialMeasure r p₀ p).map
      (fun x ↦ ((∑ i, x i : ℕ) : ℝ))).quantile u : EReal)) (𝓝[<] 1)
      (𝓝 (if r = 0 ∨ p₀ = 1 then (0 : EReal) else ⊤)) := by
  rw [map_cast_sum_negativeMultinomialMeasure, map_sum_negativeMultinomialMeasure hr hp₀ hp]
  have hp₀_le : p₀ ≤ 1 := calc
    p₀ ≤ p₀ + ∑ i, (p i : ℝ) :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ (p _).coe_nonneg)
    _ = 1 := hp
  exact tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsLT_one hr hp₀
    hp₀_le

end TauCeti.Probability
