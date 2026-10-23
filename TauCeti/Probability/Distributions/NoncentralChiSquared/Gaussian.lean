/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ChiSquared
public import TauCeti.Probability.Distributions.Gaussian.Affine
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Transforms
public import TauCeti.Probability.Moments.Determinacy

/-!
# Gaussian constructions of noncentral chi-squared laws

A sum of squares of independent unit-variance real Gaussians has noncentral chi-squared law.
Its degree is the number of coordinates and its noncentrality is the sum of squared means.
Equivalently, the squared norm of a Gaussian vector with identity covariance has noncentrality
equal to the squared norm of its mean. The empty coordinate type gives the point mass at zero.

The identification uses the Gaussian-square moment-generating function and
`TauCeti.Measure.ext_of_mgf`. The product-law equality also yields the construction for an
independent family of random variables.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

/-- The sum of squares of independent unit-variance Gaussian coordinates has noncentral
chi-squared law, including the empty family. -/
@[simp]
theorem map_sum_sq_pi_gaussianReal_noncentral (m : ι → ℝ) :
    (Measure.pi fun i ↦ gaussianReal (m i) 1).map (fun x ↦ ∑ i, x i ^ 2) =
      noncentralChiSquaredMeasure (Fintype.card ι) (∑ i, ‖m i‖₊ ^ 2) := by
  classical
  let l : ℝ≥0 := ∑ i, ‖m i‖₊ ^ 2
  have hk : (0 : ℝ) ≤ Fintype.card ι := by positivity
  let _ := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
  have hdom : (0 : ℝ) ∈ interior
      (integrableExpSet id (noncentralChiSquaredMeasure (Fintype.card ι) l)) := by
    rw [integrableExpSet_id_noncentralChiSquaredMeasure hk l]
    split_ifs <;> norm_num
  have hmeas : Measurable (fun x : ι → ℝ ↦ ∑ i, x i ^ 2) := by fun_prop
  apply (TauCeti.Measure.ext_of_mgf hdom ?_).symm
  filter_upwards [Iio_mem_nhds (by norm_num : (0 : ℝ) < 2⁻¹)] with t ht
  have ht' : t < (2⁻¹ : ℝ) := ht
  have hb : 0 < 1 - 2 * t := by linarith [ht']
  rw [mgf_id_noncentralChiSquaredMeasure hk l ht',
    mgf_id_map hmeas.aemeasurable,
    mgf_sum_pi (fun _ : ι ↦ fun x : ℝ ↦ x ^ 2)]
  simp_rw [mgf_sq_gaussianReal_one _ ht']
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    ← Real.rpow_mul_natCast hb.le, ← Real.exp_sum]
  simp only [l, NNReal.coe_sum, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs, sq_abs,
    Finset.sum_div, Finset.sum_mul]
  congr 2
  ring

/-- The squared norm of an identity-covariance Gaussian has noncentral chi-squared law with
noncentrality the squared norm of its mean. Dimension zero is included. -/
@[simp]
theorem map_norm_sq_multivariateGaussian_noncentral [DecidableEq ι]
    (m : EuclideanSpace ℝ ι) :
    (multivariateGaussian m (1 : Matrix ι ι ℝ)).map (fun x ↦ ‖x‖ ^ 2) =
      noncentralChiSquaredMeasure (Fintype.card ι) (‖m‖₊ ^ 2) := by
  have hnorm : (‖m‖₊ ^ 2 : ℝ≥0) = ∑ i, ‖m i‖₊ ^ 2 := by
    apply NNReal.eq
    simpa only [NNReal.coe_pow, coe_nnnorm, NNReal.coe_sum, Real.norm_eq_abs, sq_abs] using
      EuclideanSpace.real_norm_sq_eq m
  rw [multivariateGaussian_one_eq_map_pi,
    Measure.map_map (by fun_prop) (by fun_prop), hnorm,
    ← map_sum_sq_pi_gaussianReal_noncentral (fun i ↦ m i)]
  congr 1
  funext x
  simpa only [Function.comp_apply, WithLp.ofLp_toLp] using
    EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A finite independent family of unit-variance Gaussians gives a noncentral chi-squared
sum of squares. -/
theorem iIndepFun.hasLaw_sum_sq_gaussianReal_noncentral {ι : Type*} [Fintype ι]
    {X : ι → Ω → ℝ} {m : ι → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (gaussianReal (m i) 1) P) :
    HasLaw (fun ω ↦ ∑ i, X i ω ^ 2)
      (noncentralChiSquaredMeasure (Fintype.card ι) (∑ i, ‖m i‖₊ ^ 2)) P := by
  classical
  have hmeas : Measurable (fun x : ι → ℝ ↦ ∑ i, x i ^ 2) := by fun_prop
  exact (HasLaw.mk hmeas.aemeasurable (map_sum_sq_pi_gaussianReal_noncentral m)).fun_comp
    (hindep.hasLaw_pi hlaw)

/-- The squared norm of an identity-covariance Gaussian random vector has noncentral
chi-squared law. -/
theorem HasLaw.norm_sq_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Ω → EuclideanSpace ℝ ι} {m : EuclideanSpace ℝ ι}
    (hX : HasLaw X (multivariateGaussian m (1 : Matrix ι ι ℝ)) P) :
    HasLaw (fun ω ↦ ‖X ω‖ ^ 2)
      (noncentralChiSquaredMeasure (Fintype.card ι) (‖m‖₊ ^ 2)) P :=
  (HasLaw.mk (by fun_prop) (map_norm_sq_multivariateGaussian_noncentral m)).fun_comp hX

end ProbabilityTheory
