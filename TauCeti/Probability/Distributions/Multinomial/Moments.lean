/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Binomial.Basic
public import TauCeti.Probability.Distributions.Multinomial.Aggregation
public import TauCeti.Probability.Distributions.Multinomial.Marginal
public import TauCeti.Probability.Moments.Covariance

/-!
# Moments of the multinomial distribution

This file computes the mean and covariance of the multinomial count vector after casting it into
Euclidean space.  Each coordinate is binomial, while the sum of two distinct coordinates is
binomial with the combined cell probability.  These marginal laws determine the coordinate
means, variances, and covariances.

The entrywise calculation is also packaged as a covariance matrix and as Mathlib's basis-free
covariance bilinear form.

## Main results

* `TauCeti.Probability.integral_id_map_multinomialToEuclidean_multinomialMeasure` computes the
  Euclidean mean.
* `TauCeti.Probability.covariance_eval_map_multinomialToEuclidean_multinomialMeasure` computes
  every coordinate covariance.
* `TauCeti.Probability.covMatrix_map_multinomialToEuclidean_multinomialMeasure` gives the
  covariance matrix as a diagonal matrix minus a rank-one matrix.
* `TauCeti.Probability.covarianceBilin_map_multinomialToEuclidean_multinomialMeasure` gives the
  corresponding covariance bilinear form.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Discrete Multivariate Distributions*, Wiley,
  1997, Chapter 35.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory

open scoped NNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- A coordinate of a multinomial count vector, cast to `ℝ`, has the corresponding real-valued
binomial law. -/
private theorem hasLaw_multinomial_apply (n : ℕ) (p : StdSimplex NNReal ι) (i : ι) :
    HasLaw (fun k : ι → ℕ ↦ (k i : ℝ)) Bin(ℝ, n, p.multinomialCellProbability i)
      (multinomialMeasure n p) := by
  have hnat : HasLaw (fun k : ι → ℕ ↦ k i) Bin(n, p.multinomialCellProbability i)
      (multinomialMeasure n p) :=
    ⟨(measurable_pi_apply i).aemeasurable, map_eval_multinomialMeasure n p i⟩
  have hcast : HasLaw (fun m : ℕ ↦ (m : ℝ)) Bin(ℝ, n, p.multinomialCellProbability i)
      Bin(n, p.multinomialCellProbability i) := ⟨by fun_prop, rfl⟩
  exact hcast.fun_comp hnat

/-- A coordinate projection of the Euclidean multinomial law has the corresponding real-valued
binomial law. -/
private theorem hasLaw_apply_map_multinomialToEuclidean (n : ℕ)
    (p : StdSimplex NNReal ι) (i : ι) :
    HasLaw (fun z : EuclideanSpace ℝ ι ↦ z i) Bin(ℝ, n, p.multinomialCellProbability i)
      ((multinomialMeasure n p).map multinomialToEuclidean) := by
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_map (by fun_prop) measurable_multinomialToEuclidean]
  rw [← (hasLaw_multinomial_apply n p i).map_eq]
  apply Measure.map_congr
  filter_upwards [] with k
  simpa only [Function.comp_apply] using multinomialToEuclidean_apply k i

open Classical in
/-- Map two selected cells to `true` and all remaining cells to `false`. -/
private def pairCellMap (i j : ι) (k : ι) : Bool :=
  decide (k = i ∨ k = j)

open scoped Classical in
private theorem filter_pairCellMap_eq_pair (i j : ι) :
    Finset.univ.filter (fun x ↦ pairCellMap i j x = true) = {i, j} := by
  ext x
  simp [pairCellMap]

omit [Fintype ι] in
private theorem funOnFinite_map_pairCellMap_apply [Finite ι]
    (i j : ι) (hij : i ≠ j) (k : ι → ℕ) :
    FunOnFinite.map (pairCellMap i j) k true = k i + k j := by
  classical
  let _ := Fintype.ofFinite ι
  rw [FunOnFinite.map_apply_apply]
  rw [filter_pairCellMap_eq_pair]
  simp [hij]

omit [Fintype ι] in
private theorem weights_map_pairCellMap_apply [Finite ι]
    (p : StdSimplex NNReal ι) (i j : ι)
    (hij : i ≠ j) :
    (p.map (pairCellMap i j)).weights true = p.weights i + p.weights j := by
  classical
  let _ := Fintype.ofFinite ι
  rw [StdSimplex.weights_map, Finsupp.mapDomain_fintype]
  simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
  rw [← Finset.sum_filter, filter_pairCellMap_eq_pair]
  simp [hij]

private theorem hasLaw_multinomial_add_apply (n : ℕ) (p : StdSimplex NNReal ι)
    (i j : ι) (hij : i ≠ j) :
    HasLaw (fun k : ι → ℕ ↦ ((k i : ℝ) + k j))
      Bin(ℝ, n, (p.map (pairCellMap i j)).multinomialCellProbability true)
      (multinomialMeasure n p) := by
  have haggregate :
      HasLaw (FunOnFinite.map (M := ℕ) (pairCellMap i j))
        (multinomialMeasure n (p.map (pairCellMap i j))) (multinomialMeasure n p) :=
    ⟨(FunOnFinite.continuous_map ℕ (pairCellMap i j)).aemeasurable,
      map_funOnFinite_map_multinomialMeasure (pairCellMap i j) n p⟩
  have hcoord := hasLaw_multinomial_apply n (p.map (pairCellMap i j)) true
  have hcomp := hcoord.fun_comp haggregate
  apply hcomp.congr
  filter_upwards [] with k
  rw [funOnFinite_map_pairCellMap_apply i j hij, Nat.cast_add]

private theorem hasLaw_add_apply_map_multinomialToEuclidean (n : ℕ)
    (p : StdSimplex NNReal ι) (i j : ι) (hij : i ≠ j) :
    HasLaw (fun z : EuclideanSpace ℝ ι ↦ z i + z j)
      Bin(ℝ, n, (p.map (pairCellMap i j)).multinomialCellProbability true)
      ((multinomialMeasure n p).map multinomialToEuclidean) := by
  refine ⟨by fun_prop, ?_⟩
  rw [Measure.map_map (by fun_prop) measurable_multinomialToEuclidean]
  rw [← (hasLaw_multinomial_add_apply n p i j hij).map_eq]
  apply Measure.map_congr
  filter_upwards [] with k
  simp only [Function.comp_apply, multinomialToEuclidean_apply]

/-- The Euclidean multinomial law has a finite second moment. -/
theorem memLp_id_map_multinomialToEuclidean_multinomialMeasure (n : ℕ)
    (p : StdSimplex NNReal ι) :
    MemLp id 2 ((multinomialMeasure n p).map multinomialToEuclidean) := by
  rw [(measurableEmbedding_multinomialToEuclidean (ι := ι)).memLp_map_measure_iff]
  apply (memLp_two_iff_integrable_sq_norm (by fun_prop)).2
  simpa only [Function.id_comp] using
    integrable_multinomialMeasure (fun k ↦ ‖multinomialToEuclidean k‖ ^ 2) n p

/-- The mean of the Euclidean multinomial law is the trial count times its vector of cell
probabilities. -/
@[simp]
theorem integral_id_map_multinomialToEuclidean_multinomialMeasure (n : ℕ)
    (p : StdSimplex NNReal ι) :
    ∫ z, z ∂(multinomialMeasure n p).map multinomialToEuclidean =
      (EuclideanSpace.equiv ι ℝ).symm (fun i ↦ (n : ℝ) * p.weights i) := by
  let _ := isProbabilityMeasure_multinomialMeasure n p
  have hmem := memLp_id_map_multinomialToEuclidean_multinomialMeasure n p
  have hint : Integrable id ((multinomialMeasure n p).map multinomialToEuclidean) :=
    hmem.integrable one_le_two
  have hint' : Integrable (fun z : EuclideanSpace ℝ ι ↦ z)
      ((multinomialMeasure n p).map multinomialToEuclidean) := by
    exact hint.congr (Filter.Eventually.of_forall fun _ ↦ rfl)
  ext i
  rw [eval_integral_piLp (fun j ↦ hint'.eval_piLp j) i,
    integral_of_hasLaw_binomial (hasLaw_apply_map_multinomialToEuclidean n p i)]
  simp
  ring

/-- The variance of a coordinate of the Euclidean multinomial law is `n pᵢ (1 - pᵢ)`. -/
@[simp]
theorem variance_eval_map_multinomialToEuclidean_multinomialMeasure (n : ℕ)
    (p : StdSimplex NNReal ι) (i : ι) :
    Var[fun z : EuclideanSpace ℝ ι ↦ z i;
      (multinomialMeasure n p).map multinomialToEuclidean] =
      (n : ℝ) * p.weights i * (1 - p.weights i) := by
  rw [variance_of_hasLaw_binomial (hasLaw_apply_map_multinomialToEuclidean n p i)]
  simp
  ring

/-- Distinct coordinates of the Euclidean multinomial law have covariance `-n pᵢ pⱼ`. -/
@[simp]
theorem covariance_eval_map_multinomialToEuclidean_multinomialMeasure_of_ne (n : ℕ)
    (p : StdSimplex NNReal ι) {i j : ι} (hij : i ≠ j) :
    cov[fun z : EuclideanSpace ℝ ι ↦ z i, fun z ↦ z j;
      (multinomialMeasure n p).map multinomialToEuclidean] =
      -(n : ℝ) * p.weights i * p.weights j := by
  let μ := (multinomialMeasure n p).map multinomialToEuclidean
  let _ := isProbabilityMeasure_multinomialMeasure n p
  let _ : IsProbabilityMeasure μ := inferInstance
  have hmem := memLp_id_map_multinomialToEuclidean_multinomialMeasure n p
  have hi : MemLp (fun z : EuclideanSpace ℝ ι ↦ z i) 2 μ :=
    by simpa [μ] using hmem.continuousLinearMap_comp (𝕜 := ℝ) (EuclideanSpace.proj i)
  have hj : MemLp (fun z : EuclideanSpace ℝ ι ↦ z j) 2 μ :=
    by simpa [μ] using hmem.continuousLinearMap_comp (𝕜 := ℝ) (EuclideanSpace.proj j)
  have hadd := variance_fun_add hi hj
  rw [variance_of_hasLaw_binomial
      (hasLaw_add_apply_map_multinomialToEuclidean n p i j hij),
    variance_eval_map_multinomialToEuclidean_multinomialMeasure,
    variance_eval_map_multinomialToEuclidean_multinomialMeasure] at hadd
  rw [StdSimplex.coe_multinomialCellProbability,
    weights_map_pairCellMap_apply p i j hij] at hadd
  push_cast at hadd
  nlinarith

open scoped Classical in
/-- Every entry of the Euclidean multinomial covariance is `n (pᵢ δᵢⱼ - pᵢ pⱼ)`. -/
@[simp]
theorem covariance_eval_map_multinomialToEuclidean_multinomialMeasure
    (n : ℕ) (p : StdSimplex NNReal ι) (i j : ι) :
    cov[fun z : EuclideanSpace ℝ ι ↦ z i, fun z ↦ z j;
      (multinomialMeasure n p).map multinomialToEuclidean] =
      (n : ℝ) * ((Matrix.diagonal (fun k ↦ (p.weights k : ℝ))) i j -
        p.weights i * p.weights j) := by
  by_cases hij : i = j
  · subst j
    rw [covariance_self (by fun_prop),
      variance_eval_map_multinomialToEuclidean_multinomialMeasure]
    simp
    ring
  · rw [covariance_eval_map_multinomialToEuclidean_multinomialMeasure_of_ne n p hij]
    simp [Matrix.diagonal_apply_ne _ hij]
    ring

open scoped Classical in
/-- The covariance matrix of the Euclidean multinomial law is
`n (diag(p) - p pᵀ)`. -/
@[simp]
theorem covMatrix_map_multinomialToEuclidean_multinomialMeasure
    (n : ℕ) (p : StdSimplex NNReal ι) :
    covMatrix ((multinomialMeasure n p).map multinomialToEuclidean) =
      (n : ℝ) • (Matrix.diagonal (fun i ↦ (p.weights i : ℝ)) -
        Matrix.vecMulVec (fun i ↦ (p.weights i : ℝ)) fun i ↦ (p.weights i : ℝ)) := by
  ext i j
  rw [covMatrix_apply, covariance_eval_map_multinomialToEuclidean_multinomialMeasure]
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul]

open scoped Classical in
/-- The covariance bilinear form of the Euclidean multinomial law is represented by
`n (diag(p) - p pᵀ)`. -/
@[simp]
theorem covarianceBilin_map_multinomialToEuclidean_multinomialMeasure
    (n : ℕ) (p : StdSimplex NNReal ι) (x y : EuclideanSpace ℝ ι) :
    covarianceBilin ((multinomialMeasure n p).map multinomialToEuclidean) x y =
      ⟪x, ((n : ℝ) • (Matrix.diagonal (fun i ↦ (p.weights i : ℝ)) -
        Matrix.vecMulVec (fun i ↦ (p.weights i : ℝ)) fun i ↦
          (p.weights i : ℝ))).toEuclideanLin y⟫ := by
  let _ := isProbabilityMeasure_multinomialMeasure n p
  rw [covarianceBilin_eq_covMatrix _
      (memLp_id_map_multinomialToEuclidean_multinomialMeasure n p),
    covMatrix_map_multinomialToEuclidean_multinomialMeasure]

end TauCeti.Probability
