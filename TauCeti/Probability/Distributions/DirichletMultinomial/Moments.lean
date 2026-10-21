/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.DirichletMultinomial.Basic
public import TauCeti.Probability.Distributions.Multinomial.Moments
public import TauCeti.Probability.Distributions.Dirichlet.Moments
import TauCeti.Probability.Moments.Mixture

/-!
# Mean and covariance of Dirichlet-multinomial laws

For total concentration `A = ∑ i, a i` and cell shares `p i = a i / A`, the Euclidean
cast of a Dirichlet-multinomial count vector has mean `n p` and covariance
`n (A + n) / (A + 1) • (diag(p) - p pᵀ)`. These formulas include zero trials and
the one-category law. Finite native support supplies all integrability needed below.

The calculation uses the existing multinomial and Dirichlet moments through the law of
total covariance `covariance_bind`. The covariance is also packaged as a matrix and as
Mathlib's basis-free covariance bilinear form.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 40.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped NNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The Euclidean Dirichlet-multinomial count vector has a finite second moment, including
invalid concentrations, whose law is zero. -/
theorem memLp_id_map_multinomialToEuclidean_dirichletMultinomialMeasure
    (n : ℕ) (a : ι → ℝ) :
    MemLp id 2 ((dirichletMultinomialMeasure n a).map multinomialToEuclidean) := by
  rw [(measurableEmbedding_multinomialToEuclidean (ι := ι)).memLp_map_measure_iff]
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
  simpa only [Function.id_comp] using
    integrable_dirichletMultinomialMeasure (fun k ↦ ‖multinomialToEuclidean k‖ ^ 2) n a

/-- The mean of the Euclidean count vector is the number of trials times the normalized
concentration vector. -/
@[simp]
theorem integral_id_map_multinomialToEuclidean_dirichletMultinomialMeasure
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) :
    ∫ z, z ∂(dirichletMultinomialMeasure n a).map multinomialToEuclidean =
      (EuclideanSpace.equiv ι ℝ).symm (fun i ↦ (n : ℝ) * (a i / ∑ j, a j)) := by
  let p : EuclideanSpace ℝ ι → StdSimplex ℝ≥0 ι := fun x ↦
    (StdSimplex.single (Classical.arbitrary ι) : StdSimplex ℝ≥0 ι).extendWeights
      (fun i ↦ (x i).toNNReal)
  have hp : Measurable p := (StdSimplex.measurable_extendWeights _).comp (by fun_prop)
  have hweights := ae_extendWeights_dirichletMeasure ha
    (StdSimplex.single (Classical.arbitrary ι))
  rw [integral_map (by fun_prop) (by fun_prop),
    integral_dirichletMultinomialMeasure_eq_integral _ n p hp hweights]
  calc
    _ = ∫ x, (n : ℝ) • x ∂dirichletMeasure a := by
      apply integral_congr_ae
      filter_upwards [hweights] with x hx
      rw [← integral_map (φ := multinomialToEuclidean)
        (f := fun z : EuclideanSpace ℝ ι ↦ z) (by fun_prop) (by fun_prop),
        integral_id_map_multinomialToEuclidean_multinomialMeasure]
      ext i
      simp [p, hx]
    _ = _ := by
      rw [integral_smul, integral_id_dirichletMeasure ha]
      ext i
      simp

open scoped Classical in
private theorem covariance_cast_dirichletMultinomialMeasure {a : ι → ℝ}
    (ha : ∀ i, 0 < a i) (n : ℕ) (i j : ι) :
    cov[fun k : ι → ℕ ↦ (k i : ℝ), fun k ↦ (k j : ℝ);
      dirichletMultinomialMeasure n a] =
      (n : ℝ) * ((if i = j then a i / ∑ l, a l else 0) -
        (a i / ∑ l, a l) * (a j / ∑ l, a l)) +
      ((n : ℝ) ^ 2 - n) *
        cov[fun x ↦ x i, fun x ↦ x j; dirichletMeasure a] := by
  classical
  let _ := isProbabilityMeasure_dirichletMeasure ha
  let p : EuclideanSpace ℝ ι → StdSimplex ℝ≥0 ι := fun x ↦
    (StdSimplex.single (Classical.arbitrary ι) : StdSimplex ℝ≥0 ι).extendWeights
      (fun l ↦ (x l).toNNReal)
  have hp : Measurable p := (StdSimplex.measurable_extendWeights _).comp (by fun_prop)
  have hK : Measurable (fun x ↦ multinomialMeasure n (p x)) :=
    measurable_multinomialMeasure.comp (measurable_const.prodMk hp)
  have hweights := ae_extendWeights_dirichletMeasure ha
    (StdSimplex.single (Classical.arbitrary ι))
  have hmem (l : ι) : MemLp (fun k : ι → ℕ ↦ (k l : ℝ)) 2
      (dirichletMultinomialMeasure n a) :=
    (memLp_two_iff_integrable_sq
      (integrable_dirichletMultinomialMeasure (fun k ↦ (k l : ℝ)) n a).aestronglyMeasurable).2
      (integrable_dirichletMultinomialMeasure _ n a)
  -- Total covariance separates the mean component covariance from the covariance of cell means.
  have hmi := hmem i
  have hmj := hmem j
  rw [dirichletMultinomialMeasure_eq_bind n p hweights] at hmi hmj ⊢
  rw [covariance_bind hK (.of_forall fun _ ↦ isProbabilityMeasure_multinomialMeasure n _)
    hmi hmj]
  simp_rw [covariance_cast_apply_multinomialMeasure, integral_cast_apply_multinomialMeasure]
  have hi := (memLp_eval_dirichletMeasure (a := a) i 2).integrable one_le_two
  have hij : Integrable (fun x : EuclideanSpace ℝ ι ↦ x i * x j) (dirichletMeasure a) :=
    (memLp_eval_dirichletMeasure (a := a) i 2).integrable_mul
      (memLp_eval_dirichletMeasure (a := a) j 2)
  -- The extended weights agree almost everywhere with the original Dirichlet coordinates.
  have heq : (fun x ↦ (n : ℝ) * ((if i = j then ((p x).weights i : ℝ) else 0) -
      (p x).weights i * (p x).weights j)) =ᵐ[dirichletMeasure a]
      fun x ↦ (n : ℝ) * ((if i = j then x i else 0) - x i * x j) := by
    filter_upwards [hweights] with x hx
    simp only [p, hx]
  have hmeans (l : ι) : (fun x ↦ (n : ℝ) * ((p x).weights l : ℝ))
      =ᵐ[dirichletMeasure a] fun x ↦ (n : ℝ) * x l := by
    filter_upwards [hweights] with x hx
    rw [hx]
  -- Integrate the component covariance and combine it with the scaled Dirichlet covariance.
  rw [integral_congr_ae heq, covariance_congr_ae (hmeans i) (hmeans j),
    covariance_const_mul_left, covariance_const_mul_right, integral_const_mul]
  split_ifs with he
  · rw [integral_sub hi hij, integral_eval_dirichletMeasure ha]
    rw [integral_mul_eval_dirichletMeasure ha]
    ring
  · simp only [zero_sub, integral_neg]
    rw [integral_mul_eval_dirichletMeasure ha]
    ring

/-- A Euclidean Dirichlet-multinomial coordinate has variance `n pᵢ (1 - pᵢ) (A+n)/(A+1)`,
where `A` is the total concentration and `pᵢ = a i / A`. -/
@[simp]
theorem variance_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) (i : ι) :
    Var[fun z : EuclideanSpace ℝ ι ↦ z i;
      (dirichletMultinomialMeasure n a).map multinomialToEuclidean] =
      (n : ℝ) * (a i / ∑ l, a l) * (1 - a i / ∑ l, a l) *
        ((∑ l, a l) + n) / ((∑ l, a l) + 1) := by
  have hA : 0 < ∑ l, a l := Finset.sum_pos (fun l _ ↦ ha l) Finset.univ_nonempty
  rw [← covariance_self (by fun_prop),
    covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, multinomialToEuclidean_apply]
  rw [covariance_cast_dirichletMultinomialMeasure ha,
    covariance_self (by fun_prop), variance_eval_dirichletMeasure ha]
  simp only [ite_true]
  field_simp
  ring

/-- Distinct Euclidean Dirichlet-multinomial coordinates have covariance
`-n pᵢ pⱼ (A+n)/(A+1)`, where `A` is the total concentration and `pᵢ = a i / A`. -/
@[simp]
theorem covariance_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure_of_ne
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) {i j : ι} (hij : i ≠ j) :
    cov[fun z : EuclideanSpace ℝ ι ↦ z i, fun z ↦ z j;
      (dirichletMultinomialMeasure n a).map multinomialToEuclidean] =
      -(n : ℝ) * (a i / ∑ l, a l) * (a j / ∑ l, a l) *
        ((∑ l, a l) + n) / ((∑ l, a l) + 1) := by
  have hA : 0 < ∑ l, a l := Finset.sum_pos (fun l _ ↦ ha l) Finset.univ_nonempty
  rw [covariance_map (by fun_prop) (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, multinomialToEuclidean_apply]
  rw [covariance_cast_dirichletMultinomialMeasure ha,
    covariance_eval_dirichletMeasure_of_ne ha hij]
  simp only [hij, ite_false]
  field_simp
  ring

open scoped Classical in
/-- Each covariance entry has the multinomial covariance shape, inflated by
`(A + n) / (A + 1)` where `A` is the total concentration. -/
@[simp]
theorem covariance_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) (i j : ι) :
    cov[fun z : EuclideanSpace ℝ ι ↦ z i, fun z ↦ z j;
      (dirichletMultinomialMeasure n a).map multinomialToEuclidean] =
      ((n : ℝ) * ((∑ l, a l) + n) / ((∑ l, a l) + 1)) *
        ((Matrix.diagonal (fun l ↦ a l / ∑ k, a k)) i j -
          (a i / ∑ l, a l) * (a j / ∑ l, a l)) := by
  by_cases hij : i = j
  · subst j
    rw [covariance_self (by fun_prop),
      variance_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
    simp only [Matrix.diagonal_apply_eq]
    ring
  · rw [covariance_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure_of_ne ha n hij]
    simp only [Matrix.diagonal_apply_ne _ hij]
    ring

open scoped Classical in
/-- The covariance matrix of the Euclidean Dirichlet-multinomial count vector. -/
@[simp]
theorem covMatrix_map_multinomialToEuclidean_dirichletMultinomialMeasure
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) :
    covMatrix ((dirichletMultinomialMeasure n a).map multinomialToEuclidean) =
      ((n : ℝ) * ((∑ l, a l) + n) / ((∑ l, a l) + 1)) •
        (Matrix.diagonal (fun i ↦ a i / ∑ l, a l) -
          Matrix.vecMulVec (fun i ↦ a i / ∑ l, a l) (fun i ↦ a i / ∑ l, a l)) := by
  ext i j
  rw [covMatrix_apply,
    covariance_eval_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul]

open scoped Classical in
/-- The covariance bilinear form is represented by the Dirichlet-multinomial covariance matrix. -/
@[simp]
theorem covarianceBilin_map_multinomialToEuclidean_dirichletMultinomialMeasure
    {a : ι → ℝ} (ha : ∀ i, 0 < a i) (n : ℕ) (x y : EuclideanSpace ℝ ι) :
    covarianceBilin ((dirichletMultinomialMeasure n a).map multinomialToEuclidean) x y =
      ⟪x, (((n : ℝ) * ((∑ l, a l) + n) / ((∑ l, a l) + 1)) •
        (Matrix.diagonal (fun i ↦ a i / ∑ l, a l) -
          Matrix.vecMulVec (fun i ↦ a i / ∑ l, a l)
            (fun i ↦ a i / ∑ l, a l))).toEuclideanLin y⟫ := by
  let _ := isProbabilityMeasure_dirichletMultinomialMeasure ha n
  rw [covarianceBilin_eq_covMatrix _
    (memLp_id_map_multinomialToEuclidean_dirichletMultinomialMeasure n a),
    covMatrix_map_multinomialToEuclidean_dirichletMultinomialMeasure ha]

end TauCeti.Probability
