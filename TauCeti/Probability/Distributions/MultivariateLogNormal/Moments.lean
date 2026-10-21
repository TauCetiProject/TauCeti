/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.MultivariateLogNormal.Basic
public import TauCeti.Probability.Distributions.Gaussian.Transforms

import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Mixed real-power moments of multivariate log-normal laws

Every product of real powers of coordinates is integrable, including negative powers and
singular or invalid covariance parameters. For positive semidefinite log-covariance, its law is
scalar log-normal and its expectation is the exponential of the corresponding linear mean
plus half the covariance quadratic form. Taking logarithms instead gives a scalar Gaussian.
The coordinate means assemble into the Bochner mean vector, and the covariance formula is
provided both entrywise and as a covariance matrix and bilinear form.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A linear combination of coordinate logarithms has a scalar Gaussian law. -/
@[simp]
theorem map_inner_log_multivariateLogNormalMeasure (m q : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (multivariateLogNormalMeasure m S).map
        (fun x ↦ ⟪q, WithLp.toLp 2 (fun i ↦ Real.log (x i))⟫) =
      gaussianReal ⟪q, m⟫ (⟪q, S.toEuclideanLin q⟫).toNNReal := by
  rw [← map_inner_multivariateGaussian m q hS,
    ← map_log_multivariateLogNormalMeasure m S,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- A product of real powers of coordinates has a scalar log-normal law. Zero directional
variance gives a Dirac law, so no nonsingularity assumption is needed. -/
@[simp]
theorem map_prod_rpow_multivariateLogNormalMeasure (m q : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (multivariateLogNormalMeasure m S).map (fun x ↦ ∏ i, (x i) ^ (q i)) =
      logNormalMeasure ⟪q, m⟫ (⟪q, S.toEuclideanLin q⟫).toNNReal := by
  rw [multivariateLogNormalMeasure_def, logNormalMeasure_map_exp,
    ← map_inner_multivariateGaussian m q hS,
    Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext x
  simp only [Function.comp_apply]
  simp_rw [← Real.exp_mul]
  rw [← Real.exp_sum]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

/-- All mixed real powers are integrable, for every covariance parameter. -/
theorem integrable_prod_rpow_multivariateLogNormalMeasure (m q : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) :
    Integrable (fun x ↦ ∏ i, (x i) ^ (q i)) (multivariateLogNormalMeasure m S) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ ι ↦ ∏ i, (x i) ^ (q i)) :=
    Finset.measurable_prod _ fun i _ ↦ (by fun_prop : Measurable fun x : EuclideanSpace ℝ ι ↦
      x i).pow_const (q i)
  rw [multivariateLogNormalMeasure_def,
    integrable_map_measure hmeas.aestronglyMeasurable (by fun_prop)]
  have hint : 1 ∈ integrableExpSet (fun x ↦ ⟪q, x⟫) (multivariateGaussian m S) := by
    rw [integrableExpSet_inner_multivariateGaussian]
    trivial
  refine (integrable_of_mem_integrableExpSet hint).congr (ae_of_all _ fun x ↦ ?_)
  simp only [Function.comp_apply, one_mul]
  simp_rw [← Real.exp_mul]
  rw [← Real.exp_sum]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]

/-- The mixed real-power moment is `exp (⟪q,m⟫ + ⟪q,Sq⟫ / 2)`. -/
theorem integral_prod_rpow_multivariateLogNormalMeasure (m q : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    ∫ x, ∏ i, (x i) ^ (q i) ∂multivariateLogNormalMeasure m S =
      Real.exp (⟪q, m⟫ + ⟪q, S.toEuclideanLin q⟫ / 2) := by
  have hmeas : Measurable (fun x : EuclideanSpace ℝ ι ↦ ∏ i, (x i) ^ (q i)) :=
    Finset.measurable_prod _ fun i _ ↦ (by fun_prop : Measurable fun x : EuclideanSpace ℝ ι ↦
      x i).pow_const (q i)
  have hnonneg : 0 ≤ ⟪q, S.toEuclideanLin q⟫ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct_comm] using hS.dotProduct_mulVec_nonneg q.ofLp
  have h := integral_id_logNormalMeasure ⟪q, m⟫ (⟪q, S.toEuclideanLin q⟫).toNNReal
  rw [← map_prod_rpow_multivariateLogNormalMeasure m q hS,
    integral_map hmeas.aemeasurable (by fun_prop)] at h
  simpa [Real.coe_toNNReal _ hnonneg] using h

/-- Every real power of each coordinate is integrable, including at invalid covariances. -/
theorem integrable_rpow_eval_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (i : ι) (q : ℝ) :
    Integrable (fun x ↦ (x i) ^ q) (multivariateLogNormalMeasure m S) := by
  simpa [PiLp.single_apply] using
    integrable_prod_rpow_multivariateLogNormalMeasure m (EuclideanSpace.single i q) S

/-- Every coordinate has a finite second moment, even for the invalid-covariance fallback. -/
theorem memLp_two_eval_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) (i : ι) :
    MemLp (fun x ↦ x i) 2 (multivariateLogNormalMeasure m S) := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  simpa only [Real.rpow_two] using integrable_rpow_eval_multivariateLogNormalMeasure m S i 2

/-- The mean of each coordinate is `exp (mᵢ + Sᵢᵢ / 2)`. -/
@[simp]
theorem integral_eval_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i : ι) :
    ∫ x, x i ∂multivariateLogNormalMeasure m S = Real.exp (m i + S i i / 2) := by
  have h := integral_id_logNormalMeasure (m i) (S i i).toNNReal
  rw [← map_eval_multivariateLogNormalMeasure m hS i,
    integral_map (by fun_prop) (by fun_prop)] at h
  simpa only [id_eq, Real.coe_toNNReal _ (hS.diag_nonneg (i := i))] using h

/-- A multivariate log-normal vector is square-integrable for every covariance parameter. -/
theorem memLp_two_id_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) : MemLp id 2 (multivariateLogNormalMeasure m S) :=
  memLp_piLp_iff.mpr (memLp_two_eval_multivariateLogNormalMeasure m S)

/-- The Bochner mean is the vector of scalar log-normal means. -/
@[simp]
theorem integral_id_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    ∫ x, x ∂multivariateLogNormalMeasure m S =
      WithLp.toLp 2 (fun i ↦ Real.exp (m i + S i i / 2)) := by
  ext i
  rw [eval_integral_piLp
    (fun j ↦ (memLp_two_eval_multivariateLogNormalMeasure m S j).integrable one_le_two),
    integral_eval_multivariateLogNormalMeasure m hS]

/-- The mixed second moment, allowing the two coordinates to coincide. -/
@[simp]
theorem integral_mul_eval_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    ∫ x, x i * x j ∂multivariateLogNormalMeasure m S =
      Real.exp (m i + m j + (S i i + S j j) / 2 + S i j) := by
  have h := integral_prod_rpow_multivariateLogNormalMeasure m
    (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) hS
  have hprod : (fun x : EuclideanSpace ℝ ι ↦
      ∏ k, (x k) ^
        ((EuclideanSpace.single i 1 + EuclideanSpace.single j 1 : EuclideanSpace ℝ ι) k))
      =ᵐ[multivariateLogNormalMeasure m S] (fun x ↦ x i * x j) := by
    filter_upwards [ae_pos_multivariateLogNormalMeasure m S] with x hx
    simp only [PiLp.add_apply]
    simp_rw [Real.rpow_add (hx _)]
    rw [Finset.prod_mul_distrib]
    simp [PiLp.single_apply]
  rw [integral_congr_ae hprod] at h
  simp only [inner_add_left, inner_add_right, map_add,
    EuclideanSpace.inner_single_left, one_mul, conj_trivial] at h
  have hentry (a b : ι) : (S.toEuclideanLin (EuclideanSpace.single b 1)) a = S a b := by
    simp [Matrix.toLpLin_apply]
  simp only [hentry] at h
  have hsymm : S j i = S i j := by simpa using hS.isHermitian.apply i j
  simp only [hsymm] at h
  convert h using 1
  congr 1
  ring

/-- Coordinate covariance equals the product of the coordinate means times `exp (Sᵢⱼ) - 1`.
The formula also holds on the diagonal and at singular log-covariances. -/
@[simp]
theorem covariance_eval_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (i j : ι) :
    cov[fun x ↦ x i, fun x ↦ x j; multivariateLogNormalMeasure m S] =
      Real.exp (m i + m j + (S i i + S j j) / 2) * (Real.exp (S i j) - 1) := by
  rw [covariance_eq_sub (memLp_two_eval_multivariateLogNormalMeasure m S i)
    (memLp_two_eval_multivariateLogNormalMeasure m S j)]
  simp only [Pi.mul_apply]
  rw [integral_mul_eval_multivariateLogNormalMeasure m hS i j,
    integral_eval_multivariateLogNormalMeasure m hS i,
    integral_eval_multivariateLogNormalMeasure m hS j]
  have hmeans : (m i + S i i / 2) + (m j + S j j / 2) =
      m i + m j + (S i i + S j j) / 2 := by ring
  rw [← Real.exp_add, hmeans, Real.exp_add]
  ring

/-- The covariance matrix consists of the coordinate covariance formulas. -/
@[simp]
theorem covMatrix_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    covMatrix (multivariateLogNormalMeasure m S) =
      Matrix.of (fun i j ↦ Real.exp (m i + m j + (S i i + S j j) / 2) *
        (Real.exp (S i j) - 1)) := by
  ext i j
  simpa only [covMatrix_apply, Matrix.of_apply] using
    covariance_eval_multivariateLogNormalMeasure m hS i j

/-- The basis-free covariance bilinear form is represented by the log-normal covariance matrix. -/
theorem covarianceBilin_multivariateLogNormalMeasure (m : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (x y : EuclideanSpace ℝ ι) :
    covarianceBilin (multivariateLogNormalMeasure m S) x y =
      ⟪x, (Matrix.of (fun i j ↦ Real.exp (m i + m j + (S i i + S j j) / 2) *
        (Real.exp (S i j) - 1))).toEuclideanLin y⟫ := by
  rw [covarianceBilin_eq_covMatrix _ (memLp_two_id_multivariateLogNormalMeasure m S),
    covMatrix_multivariateLogNormalMeasure m hS]

end TauCeti.Probability
