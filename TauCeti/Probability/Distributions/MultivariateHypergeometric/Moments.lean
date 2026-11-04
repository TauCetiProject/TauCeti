/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.MultivariateHypergeometric.Aggregation
public import TauCeti.Probability.Distributions.Multinomial.Basic
public import TauCeti.Probability.Moments.Covariance

/-!
# Moments of the multivariate hypergeometric distribution

Draw `n` objects without replacement from a population of `N = ∑ i, K i` objects, `K i` of them
in category `i`, and write `pᵢ = K i / N`.  The count vector has mean `n p` and covariance

```text
  n (N - n) / (N - 1) • (diag p - p pᵀ),
```

the multinomial covariance of `n` draws with replacement times the finite-population correction
`(N - n) / (N - 1)`.  The total count drawn from a set of categories is hypergeometric, which
gives the variance of every group total; the covariance of two distinct counts then follows by
polarization from the variances of the two counts and of their sum.

All formulas hold whenever `n ≤ N`, with Lean's convention `x / 0 = 0`: for populations of size
zero or one the law is a Dirac law, so its covariance vanishes, and so does the totalized
correction factor `(N - n) / (N - 1)`.  The Euclidean mean, covariance matrix, and
covariance bilinear form use the coordinate cast `multinomialToEuclidean`.

## Main results

* `TauCeti.Probability.integral_cast_apply_multivariateHypergeometricMeasure`: the mean count.
* `TauCeti.Probability.variance_sum_cast_apply_multivariateHypergeometricMeasure`: the variance
  of the total count drawn from a set of categories.
* `TauCeti.Probability.covariance_cast_apply_multivariateHypergeometricMeasure`: the covariance of
  two counts.
* `TauCeti.Probability.covMatrix_map_multinomialToEuclidean_multivariateHypergeometricMeasure`:
  the covariance matrix.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 39.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Every real-cast count of a multivariate hypergeometric law has a finite second moment. -/
theorem memLp_cast_apply_multivariateHypergeometricMeasure (K : ι → ℕ) (n : ℕ) (i : ι) :
    MemLp (fun k : ι → ℕ ↦ (k i : ℝ)) 2 (multivariateHypergeometricMeasure K n) :=
  (memLp_two_iff_integrable_sq .of_discrete).2
    (integrable_multivariateHypergeometricMeasure _ K n)

/-- The mean of a multivariate hypergeometric count is `n K i / N`. -/
@[simp]
theorem integral_cast_apply_multivariateHypergeometricMeasure {K : ι → ℕ} {n : ℕ}
    (hn : n ≤ ∑ j, K j) (i : ι) :
    ∫ k, (k i : ℝ) ∂multivariateHypergeometricMeasure K n =
      n * K i / ∑ j, (K j : ℝ) := by
  have hKi : K i ≤ ∑ j, K j := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (K j))
    (Finset.mem_univ i)
  have h := integral_id_map_cast_hypergeometricMeasure hKi hn
  rw [← map_eval_multivariateHypergeometricMeasure, Measure.map_map (by fun_prop) (by fun_prop),
    integral_map Measurable.of_discrete.aemeasurable (by fun_prop)] at h
  simpa using h

/-- The total count drawn from a set `s` of categories of a multivariate hypergeometric law has
the hypergeometric variance `n q (1 - q) (N - n) / (N - 1)`, where `q` is the proportion of the
population in the categories of `s`. -/
theorem variance_sum_cast_apply_multivariateHypergeometricMeasure {K : ι → ℕ} {n : ℕ}
    (hn : n ≤ ∑ j, K j) (s : Finset ι) :
    Var[fun k : ι → ℕ ↦ ∑ i ∈ s, (k i : ℝ); multivariateHypergeometricMeasure K n] =
      n * ((∑ i ∈ s, (K i : ℝ)) / ∑ j, (K j : ℝ)) *
        (1 - (∑ i ∈ s, (K i : ℝ)) / ∑ j, (K j : ℝ)) *
        ((∑ j, (K j : ℝ) - n) / (∑ j, (K j : ℝ) - 1)) := by
  have hKs : ∑ i ∈ s, K i ≤ ∑ j, K j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s) fun _ _ _ ↦ Nat.zero_le _
  have h := variance_id_map_cast_hypergeometricMeasure hKs hn
  rw [← map_sum_multivariateHypergeometricMeasure, Measure.map_map (by fun_prop) (by fun_prop),
    variance_map (by fun_prop) (by fun_prop)] at h
  simpa [Function.comp_def] using h

/-- The variance of a multivariate hypergeometric count is `n pᵢ (1 - pᵢ) (N - n) / (N - 1)`,
where `pᵢ = K i / N`. -/
@[simp]
theorem variance_cast_apply_multivariateHypergeometricMeasure {K : ι → ℕ} {n : ℕ}
    (hn : n ≤ ∑ j, K j) (i : ι) :
    Var[fun k : ι → ℕ ↦ (k i : ℝ); multivariateHypergeometricMeasure K n] =
      n * ((K i : ℝ) / ∑ j, (K j : ℝ)) * (1 - (K i : ℝ) / ∑ j, (K j : ℝ)) *
        ((∑ j, (K j : ℝ) - n) / (∑ j, (K j : ℝ) - 1)) := by
  simpa using variance_sum_cast_apply_multivariateHypergeometricMeasure hn {i}

open scoped Classical in
/-- The covariance of two multivariate hypergeometric counts is
`n (N - n) / (N - 1) (pᵢ δᵢⱼ - pᵢ pⱼ)`, where `pᵢ = K i / N`. -/
@[simp]
theorem covariance_cast_apply_multivariateHypergeometricMeasure {K : ι → ℕ} {n : ℕ}
    (hn : n ≤ ∑ j, K j) (i j : ι) :
    cov[fun k : ι → ℕ ↦ (k i : ℝ), fun k ↦ (k j : ℝ); multivariateHypergeometricMeasure K n] =
      n * ((∑ l, (K l : ℝ) - n) / (∑ l, (K l : ℝ) - 1)) *
        ((if i = j then (K i : ℝ) / ∑ l, (K l : ℝ) else 0) -
          (K i : ℝ) / (∑ l, (K l : ℝ)) * ((K j : ℝ) / ∑ l, (K l : ℝ))) := by
  by_cases hij : i = j
  · subst j
    rw [covariance_self .of_discrete, variance_cast_apply_multivariateHypergeometricMeasure hn]
    simp only [↓reduceIte]
    ring
  -- Polarization: the variance of `kᵢ + kⱼ` is that of the group total over `{i, j}`.
  let _ := isProbabilityMeasure_multivariateHypergeometricMeasure K hn
  have hadd := variance_fun_add (memLp_cast_apply_multivariateHypergeometricMeasure K n i)
    (memLp_cast_apply_multivariateHypergeometricMeasure K n j)
  have hpair := variance_sum_cast_apply_multivariateHypergeometricMeasure hn {i, j}
  simp only [Finset.sum_pair hij] at hpair
  rw [hpair, variance_cast_apply_multivariateHypergeometricMeasure hn,
    variance_cast_apply_multivariateHypergeometricMeasure hn] at hadd
  simp only [hij, ↓reduceIte]
  linear_combination (-1 / 2 : ℝ) * hadd

/-- The Euclidean cast of a multivariate hypergeometric count vector has a finite second
moment. -/
theorem memLp_id_map_multinomialToEuclidean_multivariateHypergeometricMeasure (K : ι → ℕ)
    (n : ℕ) :
    MemLp id 2 ((multivariateHypergeometricMeasure K n).map multinomialToEuclidean) := by
  rw [(measurableEmbedding_multinomialToEuclidean (ι := ι)).memLp_map_measure_iff]
  apply memLp_piLp_iff.mpr
  intro i
  simpa only [Function.comp_apply, id_eq, multinomialToEuclidean_apply] using
    memLp_cast_apply_multivariateHypergeometricMeasure K n i

/-- The Euclidean multivariate hypergeometric mean is `n p`, with coordinates `n K i / N`. -/
@[simp]
theorem integral_id_map_multinomialToEuclidean_multivariateHypergeometricMeasure
    {K : ι → ℕ} {n : ℕ} (hn : n ≤ ∑ j, K j) :
    ∫ z, z ∂(multivariateHypergeometricMeasure K n).map multinomialToEuclidean =
      (EuclideanSpace.equiv ι ℝ).symm (fun i ↦ n * K i / ∑ j, (K j : ℝ)) := by
  let _ := isProbabilityMeasure_multivariateHypergeometricMeasure K hn
  rw [integral_map (by fun_prop) (by fun_prop)]
  ext i
  rw [eval_integral_piLp (fun j ↦ by
    simpa only [multinomialToEuclidean_apply] using
      (memLp_cast_apply_multivariateHypergeometricMeasure K n j).integrable one_le_two) i]
  simp [integral_cast_apply_multivariateHypergeometricMeasure hn]

open scoped Classical in
/-- The covariance matrix of the Euclidean multivariate hypergeometric law is
`n (N - n) / (N - 1) • (diag p - p pᵀ)`, where `pᵢ = K i / N`. -/
@[simp]
theorem covMatrix_map_multinomialToEuclidean_multivariateHypergeometricMeasure
    {K : ι → ℕ} {n : ℕ} (hn : n ≤ ∑ j, K j) :
    covMatrix ((multivariateHypergeometricMeasure K n).map multinomialToEuclidean) =
      (n * ((∑ j, (K j : ℝ) - n) / (∑ j, (K j : ℝ) - 1))) •
        (Matrix.diagonal (fun i ↦ (K i : ℝ) / ∑ j, (K j : ℝ)) -
          Matrix.vecMulVec (fun i ↦ (K i : ℝ) / ∑ j, (K j : ℝ))
            fun i ↦ (K i : ℝ) / ∑ j, (K j : ℝ)) := by
  ext i j
  rw [covMatrix_apply, covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
  simp only [multinomialToEuclidean_apply,
    covariance_cast_apply_multivariateHypergeometricMeasure hn, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply, smul_eq_mul]

open scoped Classical in
/-- The covariance bilinear form of the Euclidean multivariate hypergeometric law is represented
by `n (N - n) / (N - 1) • (diag p - p pᵀ)`, where `pᵢ = K i / N`. -/
@[simp]
theorem covarianceBilin_map_multinomialToEuclidean_multivariateHypergeometricMeasure
    {K : ι → ℕ} {n : ℕ} (hn : n ≤ ∑ j, K j) (x y : EuclideanSpace ℝ ι) :
    covarianceBilin ((multivariateHypergeometricMeasure K n).map multinomialToEuclidean) x y =
      ⟪x, ((n * ((∑ j, (K j : ℝ) - n) / (∑ j, (K j : ℝ) - 1))) •
        (Matrix.diagonal (fun i ↦ (K i : ℝ) / ∑ j, (K j : ℝ)) -
          Matrix.vecMulVec (fun i ↦ (K i : ℝ) / ∑ j, (K j : ℝ))
            fun i ↦ (K i : ℝ) / ∑ j, (K j : ℝ))).toEuclideanLin y⟫ := by
  let _ := isProbabilityMeasure_multivariateHypergeometricMeasure K hn
  rw [covarianceBilin_eq_covMatrix _
      (memLp_id_map_multinomialToEuclidean_multivariateHypergeometricMeasure K n),
    covMatrix_map_multinomialToEuclidean_multivariateHypergeometricMeasure hn]

end TauCeti.Probability
