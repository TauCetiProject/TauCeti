/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.NegativeMultinomial.Basic
public import TauCeti.Probability.Distributions.Multinomial.Basic
public import TauCeti.Probability.Moments.Covariance
import TauCeti.Probability.Distributions.NegativeMultinomial.FactorialMoments
import Mathlib.Data.Nat.Factorial.Cast

/-!
# Mean and covariance of negative-multinomial laws

For shape `r`, success weight `p₀`, and category weights `p`, the coordinate mean is
`r * p i / p₀`. The covariance is the sum of a diagonal matrix with these means and
the rank-one matrix with entries `r * p i * p j / p₀ ^ 2`.

The formulas include shape zero, inactive categories, and empty coordinate types. Finite
second moments are established for every parameter, including the invalid zero-measure
branches. The Euclidean mean, covariance matrix, and covariance bilinear form use the
existing coordinate cast `multinomialToEuclidean`.

The calculations specialize `integral_prod_descFactorial_negativeMultinomialMeasure`
to total orders one and two, then subtract the product of the means.

## References

* F. Ouimet, *Moments of the negative multinomial distribution*, 2022.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- Each real-cast count has a finite second moment, including invalid parameters. -/
theorem memLp_cast_apply_negativeMultinomialMeasure (r p₀ : ℝ) (p : ι → ℝ≥0) (i : ι) :
    MemLp (fun k : ι → ℕ => (k i : ℝ)) 2 (negativeMultinomialMeasure r p₀ p) := by
  classical
  apply (memLp_two_iff_integrable_sq (.of_discrete)).2
  simpa only [apply_ite, pow_zero, Fintype.prod_ite_eq'] using
    integrable_prod_pow_negativeMultinomialMeasure r p₀ p (fun j => if j = i then 2 else 0)

private theorem integral_descFactorial_cast_apply {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) (n : ℕ) :
    ∫ k : ι → ℕ, ((k i).descFactorial n : ℝ) ∂negativeMultinomialMeasure r p₀ p =
      (∏ j ∈ Finset.range n, (r + j)) * ((p i : ℝ) / p₀) ^ n := by
  classical
  simpa only [apply_ite, Nat.descFactorial_zero, Nat.cast_one, pow_zero,
    Fintype.prod_ite_eq', Fintype.sum_ite_eq'] using
    integral_prod_descFactorial_negativeMultinomialMeasure hr hp₀ hp
      (fun j => if j = i then n else 0)

/-- The mean of the real-cast count in category `i` is `r pᵢ / p₀`. -/
@[simp]
theorem integral_cast_apply_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    ∫ k : ι → ℕ, (k i : ℝ) ∂negativeMultinomialMeasure r p₀ p = r * p i / p₀ := by
  simpa [mul_div_assoc] using integral_descFactorial_cast_apply hr hp₀ hp i 1

private theorem integral_mul_cast_apply_of_ne {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) {i j : ι} (hij : i ≠ j) :
    ∫ k : ι → ℕ, (k i : ℝ) * k j ∂negativeMultinomialMeasure r p₀ p =
      r * (r + 1) * p i * p j / p₀ ^ 2 := by
  classical
  let n : ι → ℕ := fun l => (if l = i then 1 else 0) + if l = j then 1 else 0
  have hfactor (k : ι → ℕ) :
      ∏ l, ((k l).descFactorial (n l) : ℝ) = (k i : ℝ) * k j := by
    have hterm (l : ι) : ((k l).descFactorial (n l) : ℝ) =
        (if l = i then (k l : ℝ) else 1) * if l = j then (k l : ℝ) else 1 := by
      by_cases hi : l = i <;> by_cases hj : l = j <;> simp_all [n]
    simp_rw [hterm, Finset.prod_mul_distrib, Fintype.prod_ite_eq']
  have hpow : ∏ l, ((p l : ℝ) / p₀) ^ n l =
      ((p i : ℝ) / p₀) * ((p j : ℝ) / p₀) := by
    simp only [n, pow_add, Finset.prod_mul_distrib]
    simp only [apply_ite, pow_one, pow_zero, Fintype.prod_ite_eq']
  have hsum : ∑ l, n l = 2 := by simp [n, Finset.sum_add_distrib]
  have h := integral_prod_descFactorial_negativeMultinomialMeasure hr hp₀ hp n
  simp only [hfactor, hsum, hpow] at h
  rw [h]
  norm_num [Finset.prod_range_succ]
  ring

open scoped Classical in
/-- The raw second mixed moment, including its diagonal first-moment correction. -/
@[simp]
theorem integral_mul_cast_apply_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i j : ι) :
    ∫ k : ι → ℕ, (k i : ℝ) * k j ∂negativeMultinomialMeasure r p₀ p =
      (if i = j then r * p i / p₀ else 0) +
        r * (r + 1) * p i * p j / p₀ ^ 2 := by
  by_cases hij : i = j
  · subst j
    let _ := isProbabilityMeasure_negativeMultinomialMeasure hr hp₀ hp
    have hi := memLp_cast_apply_negativeMultinomialMeasure r p₀ p i
    have h := integral_descFactorial_cast_apply hr hp₀ hp i 2
    simp only [Nat.cast_descFactorial_two, mul_sub, mul_one] at h
    rw [integral_sub (f := fun k : ι → ℕ => (k i : ℝ) * k i)
      (hi.integrable_mul hi) (hi.integrable one_le_two),
      integral_cast_apply_negativeMultinomialMeasure hr hp₀ hp] at h
    norm_num [Finset.prod_range_succ, div_pow] at h
    simp only [ite_true]
    linear_combination h
  · simp only [hij, ite_false, zero_add]
    exact integral_mul_cast_apply_of_ne hr hp₀ hp hij

open scoped Classical in
/-- The covariance of two real-cast counts is the rank-one mixing contribution, plus
the mean count on the diagonal. -/
@[simp]
theorem covariance_cast_apply_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i j : ι) :
    cov[fun k : ι → ℕ => (k i : ℝ), fun k => (k j : ℝ);
      negativeMultinomialMeasure r p₀ p] =
      (if i = j then r * p i / p₀ else 0) + r * p i * p j / p₀ ^ 2 := by
  let _ := isProbabilityMeasure_negativeMultinomialMeasure hr hp₀ hp
  rw [covariance_eq_sub (memLp_cast_apply_negativeMultinomialMeasure r p₀ p i)
      (memLp_cast_apply_negativeMultinomialMeasure r p₀ p j)]
  simp only [Pi.mul_apply]
  rw [integral_mul_cast_apply_negativeMultinomialMeasure hr hp₀ hp,
    integral_cast_apply_negativeMultinomialMeasure hr hp₀ hp,
    integral_cast_apply_negativeMultinomialMeasure hr hp₀ hp]
  ring

/-- The real-cast count in category `i` has variance `r pᵢ (p₀ + pᵢ) / p₀²`. -/
@[simp]
theorem variance_cast_apply_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (i : ι) :
    Var[fun k : ι → ℕ => (k i : ℝ); negativeMultinomialMeasure r p₀ p] =
      r * p i * (p₀ + p i) / p₀ ^ 2 := by
  rw [← covariance_self (.of_discrete),
    covariance_cast_apply_negativeMultinomialMeasure hr hp₀ hp]
  simp only [ite_true]
  field_simp

/-- The Euclidean cast of a negative-multinomial count vector has finite second moment
for every parameter, including invalid zero-measure branches. -/
theorem memLp_id_map_multinomialToEuclidean_negativeMultinomialMeasure
    (r p₀ : ℝ) (p : ι → ℝ≥0) :
    MemLp id 2 ((negativeMultinomialMeasure r p₀ p).map multinomialToEuclidean) := by
  rw [(measurableEmbedding_multinomialToEuclidean (ι := ι)).memLp_map_measure_iff]
  apply memLp_piLp_iff.mpr
  intro i
  simpa only [Function.comp_apply, id_eq, multinomialToEuclidean_apply] using
    memLp_cast_apply_negativeMultinomialMeasure r p₀ p i

/-- The Euclidean negative-multinomial mean has coordinates `r pᵢ / p₀`. -/
@[simp]
theorem integral_id_map_multinomialToEuclidean_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    ∫ z, z ∂(negativeMultinomialMeasure r p₀ p).map multinomialToEuclidean =
      (EuclideanSpace.equiv ι ℝ).symm (fun i => r * p i / p₀) := by
  let _ := isProbabilityMeasure_negativeMultinomialMeasure hr hp₀ hp
  rw [integral_map (by fun_prop) (by fun_prop)]
  ext i
  rw [eval_integral_piLp (fun j => by
    simpa only [multinomialToEuclidean_apply] using
      (memLp_cast_apply_negativeMultinomialMeasure r p₀ p j).integrable one_le_two) i]
  simp [integral_cast_apply_negativeMultinomialMeasure hr hp₀ hp]

open scoped Classical in
/-- The covariance matrix of the Euclidean negative-multinomial law is
`diag(r p / p₀) + (r / p₀²) p pᵀ`. -/
@[simp]
theorem covMatrix_map_multinomialToEuclidean_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) :
    covMatrix ((negativeMultinomialMeasure r p₀ p).map multinomialToEuclidean) =
      Matrix.diagonal (fun i => r * p i / p₀) +
        (r / p₀ ^ 2) • Matrix.vecMulVec (fun i => (p i : ℝ)) (fun i => (p i : ℝ)) := by
  ext i j
  rw [covMatrix_apply, covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
  simp only [multinomialToEuclidean_apply,
    covariance_cast_apply_negativeMultinomialMeasure hr hp₀ hp, Matrix.add_apply,
    Matrix.diagonal_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  ring

open scoped Classical in
/-- The covariance bilinear form of the Euclidean negative-multinomial law is represented
by its diagonal-plus-rank-one covariance matrix. -/
@[simp]
theorem covarianceBilin_map_multinomialToEuclidean_negativeMultinomialMeasure {r p₀ : ℝ}
    (hr : 0 ≤ r) (hp₀ : 0 < p₀) {p : ι → ℝ≥0}
    (hp : p₀ + ∑ i, (p i : ℝ) = 1) (x y : EuclideanSpace ℝ ι) :
    covarianceBilin ((negativeMultinomialMeasure r p₀ p).map multinomialToEuclidean) x y =
      ⟪x, (Matrix.diagonal (fun i => r * p i / p₀) +
        (r / p₀ ^ 2) • Matrix.vecMulVec (fun i => (p i : ℝ))
          (fun i => (p i : ℝ))).toEuclideanLin y⟫ := by
  let _ := isProbabilityMeasure_negativeMultinomialMeasure hr hp₀ hp
  rw [covarianceBilin_eq_covMatrix _
    (memLp_id_map_multinomialToEuclidean_negativeMultinomialMeasure r p₀ p),
    covMatrix_map_multinomialToEuclidean_negativeMultinomialMeasure hr hp₀ hp]

end TauCeti.Probability
