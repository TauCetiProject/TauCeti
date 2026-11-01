/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Quantile
public import TauCeti.Probability.Distributions.MultivariateHypergeometric.Marginal

/-!
# Coordinate quantiles of multivariate hypergeometric laws

When `n` objects are drawn without replacement from a population with `K j` objects in category
`j`, the number drawn from category `i` is hypergeometric: the population has `N = ∑ j, K j`
objects, of which the `K i` objects of category `i` are marked. For a valid sample size
`n ≤ N`, the real lower quantile of that count at an interior level is the least count at which
the explicit finite hypergeometric cumulative sum reaches the level.

Near level zero the quantile tends to the smallest possible count `n - (N - K i)`, and near level
one it tends to the largest possible count `min (K i) n`.

## Main results

* `TauCeti.Probability.quantile_map_cast_eval_multivariateHypergeometricMeasure_eq_iff`: the
  coordinate quantile is the least crossing of the hypergeometric cumulative sum.
* `TauCeti.Probability.tendsto_quantile_map_cast_eval_multivariateHypergeometricMeasure_nhdsGT_zero`
  and
  `TauCeti.Probability.tendsto_quantile_map_cast_eval_multivariateHypergeometricMeasure_nhdsLT_one`:
  the endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997,
  Chapter 39.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] {K : ι → ℕ} {n : ℕ} {u : ℝ}

private theorem map_cast_eval_multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ) (i : ι) :
    (multivariateHypergeometricMeasure K n).map (fun k ↦ (k i : ℝ)) =
      (hypergeometricMeasure (∑ j, K j) (K i) n).map (Nat.cast : ℕ → ℝ) := by
  rw [← map_eval_multivariateHypergeometricMeasure,
    Measure.map_map measurable_from_nat (measurable_pi_apply i), Function.comp_def]

/-- A natural number is the lower quantile of the count drawn from category `i` of a valid
multivariate hypergeometric sample exactly when it is the least count whose hypergeometric
cumulative sum, for a population of `∑ j, K j` objects with `K i` marked, reaches the level. -/
theorem quantile_map_cast_eval_multivariateHypergeometricMeasure_eq_iff (hn : n ≤ ∑ j, K j)
    (i : ι) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((multivariateHypergeometricMeasure K n).map (fun x ↦ (x i : ℝ))).quantile u = k ↔
      IsLeast
        {m : ℕ | u ≤ ∑ j ∈ Finset.Iic m,
          if j ≤ n then
            ((K i).choose j : ℝ) * ((∑ l, K l - K i).choose (n - j) : ℝ) /
              ((∑ l, K l).choose n : ℝ)
          else 0}
        k := by
  rw [map_cast_eval_multivariateHypergeometricMeasure,
    quantile_map_cast_hypergeometricMeasure_eq_iff (Finset.single_le_sum (by simp)
      (Finset.mem_univ i)) hn hu]

/-- As the level tends to zero from above, the quantiles of a valid multivariate hypergeometric
coordinate tend to the smallest possible count `n - (∑ j, K j - K i)`. -/
theorem tendsto_quantile_map_cast_eval_multivariateHypergeometricMeasure_nhdsGT_zero
    (hn : n ≤ ∑ j, K j) (i : ι) :
    Tendsto (fun u ↦
      (((multivariateHypergeometricMeasure K n).map (fun x ↦ (x i : ℝ))).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (n - (∑ j, K j - K i) : ℕ)) := by
  rw [map_cast_eval_multivariateHypergeometricMeasure]
  exact tendsto_quantile_map_cast_hypergeometricMeasure_nhdsGT_zero
    (Finset.single_le_sum (by simp) (Finset.mem_univ i)) hn

/-- As the level tends to one from below, the quantiles of a valid multivariate hypergeometric
coordinate tend to the largest possible count `min (K i) n`. -/
theorem tendsto_quantile_map_cast_eval_multivariateHypergeometricMeasure_nhdsLT_one
    (hn : n ≤ ∑ j, K j) (i : ι) :
    Tendsto (fun u ↦
      (((multivariateHypergeometricMeasure K n).map (fun x ↦ (x i : ℝ))).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (min (K i) n : ℕ)) := by
  rw [map_cast_eval_multivariateHypergeometricMeasure]
  exact tendsto_quantile_map_cast_hypergeometricMeasure_nhdsLT_one
    (Finset.single_le_sum (by simp) (Finset.mem_univ i)) hn

end TauCeti.Probability
