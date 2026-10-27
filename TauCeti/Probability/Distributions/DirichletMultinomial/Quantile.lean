/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.DirichletMultinomial.Aggregation
public import TauCeti.Probability.Distributions.BetaBinomial.Quantile
public import TauCeti.Probability.Distributions.Dirac

/-!
# Coordinate quantiles of Dirichlet-multinomial laws

With at least two categories, a real-cast coordinate has a beta-binomial law. Its cdf is a
finite Beta-function cumulative sum, and its interior quantiles are the least counts at which
that sum reaches the level. The one-sided quantile limits are zero and the trial count.
With one category the coordinate is constantly the trial count. All statements include zero
trials, and no quantile value at an endpoint probability is assigned.

The marginal identity `map_eval_dirichletMultinomialMeasure` transfers the existing
beta-binomial cdf and quantile theory to coordinates, without introducing a multivariate cdf
or joint quantile.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 40.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι]
variable {a : ι → ℝ} {u : ℝ}

/-- The cdf of a coordinate vanishes below zero and otherwise sums its beta-binomial
masses through the natural floor. The negative branch precedes the floor. -/
theorem cdf_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure
    [DecidableEq ι] [Nontrivial ι] (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) (x : ℝ) :
    cdf (((dirichletMultinomialMeasure n a).map multinomialToEuclidean).map
      (fun z ↦ z i)) x =
      if x < 0 then 0 else ∑ j ∈ Finset.Iic ⌊x⌋₊,
        n.choose j * beta (a i + j) ((∑ l with l ≠ i, a l) + (n - j)) /
          beta (a i) (∑ l with l ≠ i, a l) := by
  rw [map_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
  split_ifs with hx
  · exact cdf_map_cast_betaBinomialMeasure_of_neg (ha i)
      (Finset.sum_pos (fun j _ ↦ ha j)
        (by simpa [Finset.filter_nonempty_iff] using exists_ne i)) n hx
  · exact cdf_map_cast_betaBinomialMeasure (ha i)
      (Finset.sum_pos (fun j _ ↦ ha j)
        (by simpa [Finset.filter_nonempty_iff] using exists_ne i)) n (le_of_not_gt hx)

/-- A coordinate quantile is exactly the least natural crossing of its explicit
beta-binomial cumulative sum, including levels equal to cumulative masses. -/
theorem quantile_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure_eq_iff
    [DecidableEq ι] [Nontrivial ι] (ha : ∀ i, 0 < a i) (hu : u ∈ Ioo 0 1)
    (n k : ℕ) (i : ι) :
    (((dirichletMultinomialMeasure n a).map multinomialToEuclidean).map
      (fun z ↦ z i)).quantile u = k ↔
      IsLeast {m : ℕ | u ≤ ∑ j ∈ Finset.Iic m,
        n.choose j * beta (a i + j) ((∑ l with l ≠ i, a l) + (n - j)) /
          beta (a i) (∑ l with l ≠ i, a l)} k := by
  rw [map_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
  exact quantile_map_cast_betaBinomialMeasure_eq_iff (ha i)
    (Finset.sum_pos (fun j _ ↦ ha j)
      (by simpa [Finset.filter_nonempty_iff] using exists_ne i)) hu n k

/-- A coordinate quantile is zero exactly through the mass at zero. -/
theorem quantile_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure_eq_zero_iff
    [DecidableEq ι] [Nontrivial ι] (ha : ∀ i, 0 < a i) (hu : u ∈ Ioo 0 1)
    (n : ℕ) (i : ι) :
    (((dirichletMultinomialMeasure n a).map multinomialToEuclidean).map
      (fun z ↦ z i)).quantile u = 0 ↔
      u ≤ beta (a i) ((∑ l with l ≠ i, a l) + n) /
        beta (a i) (∑ l with l ≠ i, a l) := by
  rw [map_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
  exact quantile_map_cast_betaBinomialMeasure_eq_zero_iff (ha i)
    (Finset.sum_pos (fun j _ ↦ ha j)
      (by simpa [Finset.filter_nonempty_iff] using exists_ne i)) hu

/-- Above one minus the mass at the trial count, the coordinate quantile is that count. -/
theorem quantile_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure_eq_upper
    [DecidableEq ι] [Nontrivial ι] (ha : ∀ i, 0 < a i) (hu : u ∈ Ioo 0 1)
    (n : ℕ) (i : ι)
    (hlevel : 1 - beta (a i + n) (∑ l with l ≠ i, a l) /
      beta (a i) (∑ l with l ≠ i, a l) < u) :
    (((dirichletMultinomialMeasure n a).map multinomialToEuclidean).map
      (fun z ↦ z i)).quantile u = n := by
  rw [map_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
  exact quantile_map_cast_betaBinomialMeasure_eq_upper (ha i)
    (Finset.sum_pos (fun j _ ↦ ha j)
      (by simpa [Finset.filter_nonempty_iff] using exists_ne i)) hu hlevel

/-- As the level tends to zero from above, coordinate quantiles tend to zero with at least
two categories, and to the trial count with one category. -/
theorem tendsto_quantile_map_cast_eval_dirichletMultinomialMeasure_nhdsGT_zero
    (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    Tendsto (fun u ↦
      ((((dirichletMultinomialMeasure n a).map multinomialToEuclidean).map
        (fun z ↦ z i)).quantile u : EReal))
      (𝓝[>] 0) (𝓝 (if Fintype.card ι = 1 then (n : EReal) else 0)) := by
  classical
  cases subsingleton_or_nontrivial ι
  · let : Unique ι := uniqueOfSubsingleton i
    simp only [Fintype.card_unique, ite_true,
      dirichletMultinomialMeasure_eq_dirac_of_subsingleton ha,
      Measure.map_dirac, multinomialToEuclidean_apply]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with u hu
    rw [Measure.quantile_dirac _ hu.1 hu.2.le]
    norm_cast
  · rw [ite_eq_right (ne_of_gt Fintype.one_lt_card),
      map_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
    exact tendsto_quantile_map_cast_betaBinomialMeasure_nhdsGT_zero (ha i)
      (Finset.sum_pos (fun j _ ↦ ha j)
        (by simpa [Finset.filter_nonempty_iff] using exists_ne i)) n

/-- As the level tends to one from below, every coordinate quantile tends to the trial
count, including one category and zero trials. -/
theorem tendsto_quantile_map_cast_eval_dirichletMultinomialMeasure_nhdsLT_one
    (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    Tendsto (fun u ↦
      ((((dirichletMultinomialMeasure n a).map multinomialToEuclidean).map
        (fun z ↦ z i)).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (n : EReal)) := by
  classical
  cases subsingleton_or_nontrivial ι
  · simp only [dirichletMultinomialMeasure_eq_dirac_of_subsingleton ha,
      Measure.map_dirac, multinomialToEuclidean_apply]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsLT zero_lt_one] with u hu
    rw [Measure.quantile_dirac _ hu.1 hu.2.le]
    norm_cast
  · rw [map_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
    exact tendsto_quantile_map_cast_betaBinomialMeasure_nhdsLT_one (ha i)
      (Finset.sum_pos (fun j _ ↦ ha j)
        (by simpa [Finset.filter_nonempty_iff] using exists_ne i)) n

end TauCeti.Probability
