/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Hypergeometric.Basic
public import TauCeti.Probability.Distributions.MultivariateHypergeometric.Basic

/-!
# Coordinate marginals of the multivariate hypergeometric distribution

In a sample drawn without replacement from a population with `K j` objects in category `j`,
the number of objects drawn from one category `i` only distinguishes category `i` from the rest
of the population.  It therefore has the scalar hypergeometric law with population size
`∑ j, K j` and `K i` marked objects.  This file proves that statement at the level of measures,
for all category sizes and sample sizes: when the sample is larger than the population, both
laws are zero.

## Main results

* `TauCeti.Probability.map_eval_multivariateHypergeometricMeasure`: a coordinate marginal of the
  multivariate hypergeometric law is hypergeometric.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 39.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The count drawn from a fixed category of a multivariate hypergeometric sample is
hypergeometric: the population size is the total of the category sizes, and the marked objects
are those of the chosen category. -/
theorem map_eval_multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ) (i : ι) :
    (multivariateHypergeometricMeasure K n).map (fun k ↦ k i) =
      hypergeometricMeasure (∑ j, K j) (K i) n := by
  classical
  by_cases hn : n ≤ ∑ j, K j
  swap
  · rw [multivariateHypergeometricMeasure_eq_zero_of_lt (lt_of_not_ge hn), Measure.map_zero,
      hypergeometricMeasure_eq_zero_of_invalid (by omega)]
  have hKi : K i ≤ ∑ j, K j := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (K j))
    (Finset.mem_univ i)
  have hrest : ∑ j ∈ Finset.univ.erase i, K j = ∑ j, K j - K i := by
    have := Finset.add_sum_erase Finset.univ K (Finset.mem_univ i)
    omega
  apply Measure.ext_of_singleton
  intro m
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.singleton m),
    multivariateHypergeometricMeasure_def, Measure.finsetSum_apply,
    hypergeometricMeasure_singleton hKi hn]
  simp only [Measure.smul_apply, Measure.dirac_apply, Set.indicator, Pi.one_apply,
    Set.mem_preimage, Set.mem_singleton_iff, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  calc
    _ = ∑ k ∈ Finset.piAntidiag Finset.univ n with k i = m,
        (∏ j, ((K j).choose (k j) : ℝ≥0∞)) * ((∑ j, K j).choose n : ℝ≥0∞)⁻¹ := by
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      rw [multivariateHypergeometricWeight_def, div_eq_mul_inv,
        (Finset.mem_piAntidiag.mp (Finset.mem_filter.mp hk).1).1]
    _ = ((if m ≤ n then (K i).choose m * (∑ j ∈ Finset.univ.erase i, K j).choose (n - m)
          else 0 : ℕ) : ℝ≥0∞) * ((∑ j, K j).choose n : ℝ≥0∞)⁻¹ := by
      rw [← Finset.sum_mul, ← Finset.sum_filter_piAntidiag_prod_choose (Finset.mem_univ i)]
      norm_cast
    _ = _ := by
      rw [hrest]
      split_ifs with hm <;> simp [hm, div_eq_mul_inv]

end TauCeti.Probability
