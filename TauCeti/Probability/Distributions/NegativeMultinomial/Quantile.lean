/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.NegativeBinomial.Quantile
public import TauCeti.Probability.Distributions.NegativeMultinomial.Aggregation

/-!
# Coordinate and total quantiles of negative-multinomial laws

For shape `r`, stopping probability `p₀` and category weights `p`, the count in category `i` of
a negative-multinomial vector is negative binomial with shape `r` and success probability
`p₀ / (p₀ + p i)`, and the total count is negative binomial with shape `r` and success
probability `p₀`. For positive shape, the real lower quantile of either count at an interior
level is the least index at which the regularized incomplete Beta cumulative mass reaches the
level.

Both counts have lower support endpoint zero. The upper endpoint of a coordinate is infinite
unless the shape or the category weight vanishes, and that of the total is infinite unless the
shape vanishes or the stopping probability is one; in those cases the count is almost surely
zero.

## Main results

* `TauCeti.Probability.quantile_map_cast_eval_negativeMultinomialMeasure_eq_iff` and
  `TauCeti.Probability.quantile_map_cast_sum_negativeMultinomialMeasure_eq_iff`: the coordinate
  and total quantiles are least incomplete-Beta crossings.
* `TauCeti.Probability.tendsto_quantile_map_cast_eval_negativeMultinomialMeasure_nhdsLT_one` and
  `TauCeti.Probability.tendsto_quantile_map_cast_sum_negativeMultinomialMeasure_nhdsLT_one`: the
  upper endpoint limits, with the matching lower endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997,
  Chapter 36.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {r p₀ u : ℝ} {p : ι → ℝ≥0}

private theorem map_cast_eval_negativeMultinomialMeasure (hr : 0 ≤ r) (hp₀ : 0 < p₀)
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    (negativeMultinomialMeasure r p₀ p).map (fun k ↦ (k i : ℝ)) =
      (negativeBinomialMeasure r (p₀ / (p₀ + p i))).map (Nat.cast : ℕ → ℝ) := by
  rw [← map_eval_negativeMultinomialMeasure hr hp₀ hp i,
    Measure.map_map measurable_from_nat (measurable_pi_apply i), Function.comp_def]

private theorem map_cast_sum_negativeMultinomialMeasure (hr : 0 ≤ r) (hp₀ : 0 < p₀)
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    (negativeMultinomialMeasure r p₀ p).map (fun k ↦ ((∑ i, k i : ℕ) : ℝ)) =
      (negativeBinomialMeasure r p₀).map (Nat.cast : ℕ → ℝ) := by
  rw [← map_sum_negativeMultinomialMeasure hr hp₀ hp,
    Measure.map_map measurable_from_nat (by fun_prop), Function.comp_def]

/-! ### Coordinates -/

/-- For positive shape, a natural number is the lower quantile of the count in category `i` of a
negative-multinomial law exactly when it is the least index whose incomplete-Beta cumulative mass,
at success probability `p₀ / (p₀ + p i)`, reaches the level. -/
theorem quantile_map_cast_eval_negativeMultinomialMeasure_eq_iff (hr : 0 < r) (hp₀ : 0 < p₀)
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((negativeMultinomialMeasure r p₀ p).map (fun x ↦ (x i : ℝ))).quantile u = k ↔
      IsLeast {j : ℕ | u ≤ regularizedIncompleteBeta r (j + 1) (p₀ / (p₀ + p i))} k := by
  rw [map_cast_eval_negativeMultinomialMeasure hr.le hp₀ hp,
    quantile_map_cast_negativeBinomialMeasure_eq_iff hr (by positivity)
      (div_le_one_of_le₀ (le_add_of_nonneg_right (p i).coe_nonneg) (by positivity)) hu]

/-- As the level tends to zero from above, the quantiles of a negative-multinomial coordinate
tend to zero. -/
theorem tendsto_quantile_map_cast_eval_negativeMultinomialMeasure_nhdsGT_zero (hr : 0 ≤ r)
    (hp₀ : 0 < p₀) (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    Tendsto ((negativeMultinomialMeasure r p₀ p).map (fun x ↦ (x i : ℝ))).quantile
      (𝓝[>] 0) (𝓝 0) := by
  rw [map_cast_eval_negativeMultinomialMeasure hr hp₀ hp]
  exact tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsGT_zero hr (by positivity)
    (div_le_one_of_le₀ (le_add_of_nonneg_right (p i).coe_nonneg) (by positivity))

/-- As the level tends to one from below, the quantiles of a negative-multinomial coordinate tend
to positive infinity, unless the shape or the category weight vanishes, when they remain at
zero. -/
theorem tendsto_quantile_map_cast_eval_negativeMultinomialMeasure_nhdsLT_one (hr : 0 ≤ r)
    (hp₀ : 0 < p₀) (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    Tendsto (fun v ↦
      (((negativeMultinomialMeasure r p₀ p).map (fun x ↦ (x i : ℝ))).quantile v : EReal))
      (𝓝[<] 1) (𝓝 (if r = 0 ∨ p i = 0 then (0 : EReal) else ⊤)) := by
  have hprob : p₀ / (p₀ + p i) = 1 ↔ p i = 0 := by
    rw [div_eq_one_iff_eq (by positivity), left_eq_add, NNReal.coe_eq_zero]
  rw [map_cast_eval_negativeMultinomialMeasure hr hp₀ hp]
  simpa only [hprob] using tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsLT_one hr
    (show 0 < p₀ / (p₀ + p i) by positivity)
    (div_le_one_of_le₀ (le_add_of_nonneg_right (p i).coe_nonneg) (by positivity))

/-! ### Total count -/

/-- For positive shape, a natural number is the lower quantile of the total count of a
negative-multinomial law exactly when it is the least index whose incomplete-Beta cumulative
mass, at success probability `p₀`, reaches the level. -/
theorem quantile_map_cast_sum_negativeMultinomialMeasure_eq_iff (hr : 0 < r) (hp₀ : 0 < p₀)
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((negativeMultinomialMeasure r p₀ p).map (fun x ↦ ((∑ i, x i : ℕ) : ℝ))).quantile u =
        k ↔
      IsLeast {j : ℕ | u ≤ regularizedIncompleteBeta r (j + 1) p₀} k := by
  have hp₀_le_one : p₀ ≤ 1 :=
    hp ▸ le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ (p i).coe_nonneg)
  rw [map_cast_sum_negativeMultinomialMeasure hr.le hp₀ hp,
    quantile_map_cast_negativeBinomialMeasure_eq_iff hr hp₀ hp₀_le_one hu]

/-- As the level tends to zero from above, the quantiles of the total count of a
negative-multinomial law tend to zero. -/
theorem tendsto_quantile_map_cast_sum_negativeMultinomialMeasure_nhdsGT_zero (hr : 0 ≤ r)
    (hp₀ : 0 < p₀) (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    Tendsto
      ((negativeMultinomialMeasure r p₀ p).map (fun x ↦ ((∑ i, x i : ℕ) : ℝ))).quantile
      (𝓝[>] 0) (𝓝 0) := by
  have hp₀_le_one : p₀ ≤ 1 :=
    hp ▸ le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ (p i).coe_nonneg)
  rw [map_cast_sum_negativeMultinomialMeasure hr hp₀ hp]
  exact tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsGT_zero hr hp₀ hp₀_le_one

/-- As the level tends to one from below, the quantiles of the total count of a
negative-multinomial law tend to positive infinity, unless the shape vanishes or the stopping
probability is one, when they remain at zero. -/
theorem tendsto_quantile_map_cast_sum_negativeMultinomialMeasure_nhdsLT_one (hr : 0 ≤ r)
    (hp₀ : 0 < p₀) (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    Tendsto (fun v ↦
      (((negativeMultinomialMeasure r p₀ p).map
        (fun x ↦ ((∑ i, x i : ℕ) : ℝ))).quantile v : EReal))
      (𝓝[<] 1) (𝓝 (if r = 0 ∨ p₀ = 1 then (0 : EReal) else ⊤)) := by
  have hp₀_le_one : p₀ ≤ 1 :=
    hp ▸ le_add_of_nonneg_right (Finset.sum_nonneg fun i _ ↦ (p i).coe_nonneg)
  rw [map_cast_sum_negativeMultinomialMeasure hr hp₀ hp]
  exact tendsto_quantile_map_cast_negativeBinomialMeasure_nhdsLT_one hr hp₀ hp₀_le_one

end TauCeti.Probability
