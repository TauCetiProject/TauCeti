/-
Copyright (c) 2026 Tau Ceti Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.OrderStatistic.Basic

/-!
# Quantiles of iid order statistics

For a sample of size `n` from a real probability law `μ`, the lower quantile of its
`k`-th order statistic is `μ.quantile` evaluated at the inverse regularized incomplete
Beta function with shapes `k + 1` and `n - k`. The index `k : Fin n` is zero-based.

The formula holds for every interior probability level, including when `μ` has atoms
or its quantile has jumps. It follows from the order-statistic cdf and the quantile
adjunction, so it requires no continuity assumption on the source law or its quantile.

## Main results

* `quantile_map_orderStatistic_pi` computes the quantile of the product-measure law.
* `quantile_of_hasLaw_orderStatistic_iid` gives the same formula for an independent sample.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, §2.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace TauCeti.Probability

variable {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ}

/-- The lower quantile of the `k`-th order statistic of an iid sample is the source
quantile at the corresponding inverse-Beta level. Atoms and discontinuous source
quantiles are allowed. -/
@[simp]
theorem quantile_map_orderStatistic_pi (k : Fin n) (hu : u ∈ Ioo 0 1) :
    ((Measure.pi fun _ : Fin n => μ).map (orderStatistic k)).quantile u =
      μ.quantile (inverseRegularizedIncompleteBeta ((k : ℝ) + 1) ((n : ℝ) - k) u) := by
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (n : ℝ) - k := sub_pos.mpr (by exact_mod_cast k.isLt)
  apply Measure.quantile_eq_of_le_cdf_iff
  intro x
  rw [cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta,
    inverseRegularizedIncompleteBeta_le_iff ha hb hu.1 hu.2]

/-- The quantile formula for the `k`-th order statistic of independent real random
variables with common law `μ`, with no atomlessness or continuity hypothesis. -/
theorem quantile_of_hasLaw_orderStatistic_iid {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Fin n → Ω → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (k : Fin n) (hu : u ∈ Ioo 0 1) :
    (P.map (fun ω => orderStatistic k fun i => X i ω)).quantile u =
      μ.quantile (inverseRegularizedIncompleteBeta ((k : ℝ) + 1) ((n : ℝ) - k) u) := by
  have hstat := (hasLaw_map (measurable_orderStatistic k).aemeasurable).comp
    (hindep.hasLaw_pi hlaw)
  simp only [Function.comp_def] at hstat
  rw [hstat.map_eq]
  exact quantile_map_orderStatistic_pi k hu

end TauCeti.Probability
