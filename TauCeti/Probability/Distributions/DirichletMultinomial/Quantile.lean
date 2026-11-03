/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.BetaBinomial.Quantile
public import TauCeti.Probability.Distributions.DirichletMultinomial.Aggregation

/-!
# Coordinate quantiles of Dirichlet-multinomial laws

With at least two categories and positive concentrations `a`, the count in category `i` of a
Dirichlet-multinomial vector with `n` trials is beta-binomial with `n` trials and shapes `a i`
and `∑ j ≠ i, a j`. Its real lower quantile at an interior level is therefore the least count at
which the explicit finite beta-binomial cumulative sum reaches the level. Near level zero the
quantile tends to zero, and near level one it tends to `n`.

## Main results

* `TauCeti.Probability.quantile_map_cast_eval_dirichletMultinomialMeasure_eq_iff`: the coordinate
  quantile is the least crossing of the beta-binomial cumulative sum.
* `TauCeti.Probability.tendsto_quantile_map_cast_eval_dirichletMultinomialMeasure_nhdsGT_zero`
  and `TauCeti.Probability.tendsto_quantile_map_cast_eval_dirichletMultinomialMeasure_nhdsLT_one`:
  the endpoint limits.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley, 1997,
  Chapter 35, Section 13.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] {a : ι → ℝ} {u : ℝ}

private theorem map_cast_eval_dirichletMultinomialMeasure (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    (dirichletMultinomialMeasure n a).map (fun k ↦ (k i : ℝ)) =
      (betaBinomialMeasure n (a i) (∑ j with j ≠ i, a j)).map (Nat.cast : ℕ → ℝ) := by
  rw [← map_eval_dirichletMultinomialMeasure ha n i,
    Measure.map_map measurable_from_nat (measurable_pi_apply i), Function.comp_def]

/-- A natural number is the lower quantile of the count in category `i` of a Dirichlet-multinomial
law exactly when it is the least count whose beta-binomial cumulative sum, with shapes `a i` and
`∑ j ≠ i, a j`, reaches the level. -/
theorem quantile_map_cast_eval_dirichletMultinomialMeasure_eq_iff (ha : ∀ i, 0 < a i) (n : ℕ)
    (i : ι) (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((dirichletMultinomialMeasure n a).map (fun x ↦ (x i : ℝ))).quantile u = k ↔
      IsLeast {m : ℕ | u ≤ ∑ j ∈ Finset.Iic m,
        n.choose j * beta (a i + j) ((∑ l with l ≠ i, a l) + (n - j)) /
          beta (a i) (∑ l with l ≠ i, a l)} k := by
  obtain ⟨j, hj⟩ := exists_ne i
  have hsum : 0 < ∑ j with j ≠ i, a j :=
    Finset.sum_pos (fun k _ ↦ ha k) ⟨j, by simp [hj]⟩
  rw [map_cast_eval_dirichletMultinomialMeasure ha,
    quantile_map_cast_betaBinomialMeasure_eq_iff (ha i) hsum hu]

omit [DecidableEq ι] in
/-- As the level tends to zero from above, the quantiles of a Dirichlet-multinomial coordinate
tend to zero. -/
theorem tendsto_quantile_map_cast_eval_dirichletMultinomialMeasure_nhdsGT_zero
    (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    Tendsto (fun u ↦
      (((dirichletMultinomialMeasure n a).map (fun x ↦ (x i : ℝ))).quantile u : EReal))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  have hsum : 0 < ∑ j with j ≠ i, a j :=
    Finset.sum_pos (fun k _ ↦ ha k) ⟨j, by simp [hj]⟩
  rw [map_cast_eval_dirichletMultinomialMeasure ha]
  exact tendsto_quantile_map_cast_betaBinomialMeasure_nhdsGT_zero (ha i) hsum n

omit [DecidableEq ι] in
/-- As the level tends to one from below, the quantiles of a Dirichlet-multinomial coordinate
tend to the number of trials. -/
theorem tendsto_quantile_map_cast_eval_dirichletMultinomialMeasure_nhdsLT_one
    (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    Tendsto (fun u ↦
      (((dirichletMultinomialMeasure n a).map (fun x ↦ (x i : ℝ))).quantile u : EReal))
      (𝓝[<] 1) (𝓝 (n : EReal)) := by
  classical
  obtain ⟨j, hj⟩ := exists_ne i
  have hsum : 0 < ∑ j with j ≠ i, a j :=
    Finset.sum_pos (fun k _ ↦ ha k) ⟨j, by simp [hj]⟩
  rw [map_cast_eval_dirichletMultinomialMeasure ha]
  exact tendsto_quantile_map_cast_betaBinomialMeasure_nhdsLT_one (ha i) hsum n

end TauCeti.Probability
