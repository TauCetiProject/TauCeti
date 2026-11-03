/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Quantile
public import TauCeti.Probability.Distributions.MultivariateHypergeometric.Marginal

/-!
# Quantiles of multivariate hypergeometric coordinates

A coordinate of a multivariate hypergeometric count vector has a scalar hypergeometric law: its
marked population is the corresponding category and its total population is the sum of all
category sizes. Therefore the real-cast coordinate quantile is the scalar least cumulative
crossing.

For a valid sample size, the one-sided endpoint limits are the smallest count forced into the
category and the largest possible count from that category.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 39.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem map_cast_eval_multivariateHypergeometricMeasure
    (K : ι → ℕ) (n : ℕ) (i : ι) :
    (multivariateHypergeometricMeasure K n).map (fun k ↦ (k i : ℝ)) =
      ((multivariateHypergeometricMeasure K n).map (fun k ↦ k i)).map
        (Nat.cast : ℕ → ℝ) := by
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The real-cast quantile of a multivariate hypergeometric coordinate is the quantile of its
scalar hypergeometric marginal. -/
theorem quantile_map_cast_eval_multivariateHypergeometricMeasure
    (K : ι → ℕ) (n : ℕ) (i : ι) (u : ℝ) :
    ((multivariateHypergeometricMeasure K n).map (fun k ↦ (k i : ℝ))).quantile u =
      ((hypergeometricMeasure (∑ j, K j) (K i) n).map
        (Nat.cast : ℕ → ℝ)).quantile u := by
  rw [map_cast_eval_multivariateHypergeometricMeasure,
    map_eval_multivariateHypergeometricMeasure]

/-- At level zero, a coordinate quantile tends to the number of objects from that category
forced into a valid sample. -/
theorem tendsto_quantile_map_cast_eval_multivariateHypergeometricMeasure_nhdsGT_zero
    (K : ι → ℕ) {n : ℕ} (hn : n ≤ ∑ j, K j) (i : ι) :
    Tendsto (fun u ↦
      (((multivariateHypergeometricMeasure K n).map (fun k ↦ (k i : ℝ))).quantile u :
        EReal))
      (𝓝[>] 0) (𝓝 (n - ((∑ j, K j) - K i) : ℕ)) := by
  have hKi : K i ≤ ∑ j, K j :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (K j)) (Finset.mem_univ i)
  rw [map_cast_eval_multivariateHypergeometricMeasure,
    map_eval_multivariateHypergeometricMeasure]
  exact tendsto_quantile_map_cast_hypergeometricMeasure_nhdsGT_zero hKi hn

/-- At level one, a coordinate quantile tends to the largest number of objects from that
category that can occur in a valid sample. -/
theorem tendsto_quantile_map_cast_eval_multivariateHypergeometricMeasure_nhdsLT_one
    (K : ι → ℕ) {n : ℕ} (hn : n ≤ ∑ j, K j) (i : ι) :
    Tendsto (fun u ↦
      (((multivariateHypergeometricMeasure K n).map (fun k ↦ (k i : ℝ))).quantile u :
        EReal))
      (𝓝[<] 1) (𝓝 (min (K i) n : ℕ)) := by
  have hKi : K i ≤ ∑ j, K j :=
    Finset.single_le_sum (fun j _ ↦ Nat.zero_le (K j)) (Finset.mem_univ i)
  rw [map_cast_eval_multivariateHypergeometricMeasure,
    map_eval_multivariateHypergeometricMeasure]
  exact tendsto_quantile_map_cast_hypergeometricMeasure_nhdsLT_one hKi hn

end TauCeti.Probability
