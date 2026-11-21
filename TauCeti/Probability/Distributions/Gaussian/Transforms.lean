/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Basic

import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.SubGaussian

/-!
# Moment- and cumulant-generating functions of Gaussian linear functionals

This file proves that every almost everywhere measurable continuous linear functional of a
Gaussian measure has finite exponential moments of every real order and computes its
moment-generating function. It then specializes the general result to inner products against a
multivariate Gaussian vector, expressing the variance as the covariance-matrix quadratic form,
and computes the corresponding cumulant-generating function.

The general results require no norm on the source space. Almost everywhere measurability of
the functional suffices; the default proof handles continuous functionals when open sets are
measurable, including sigma algebras larger than the Borel sigma algebra.

## Main results

* `ProbabilityTheory.IsGaussian.integrableExpSet_dual` identifies the exponential-integrability
  domain of an almost everywhere measurable continuous linear functional of a Gaussian measure
  with all of `ℝ`.
* `ProbabilityTheory.IsGaussian.mgf_dual` computes the moment-generating function of an almost
  everywhere measurable continuous linear functional of a Gaussian measure from its mean and
  variance.
* `ProbabilityTheory.IsGaussian.lintegral_ofReal_exp_mul_dual` gives the same exponential
  moment as a nonnegative integral.
* `TauCeti.Probability.integrableExpSet_inner_multivariateGaussian` gives the exact domain for a
  directional
  functional of a multivariate Gaussian.
* `TauCeti.Probability.map_inner_multivariateGaussian` identifies scalar linear projections.
* `TauCeti.Probability.mgf_inner_multivariateGaussian` gives the corresponding closed formula.
* `TauCeti.Probability.cgf_inner_multivariateGaussian` gives its real logarithm, the quadratic
  polynomial determined by the directional mean and variance.
* `TauCeti.Probability.integral_exp_int_mul_sin_gaussianReal` shows that the sine at frequency
  `2π` is orthogonal to every integer-exponent exponential under the standard Gaussian law.
* `TauCeti.Probability.integral_cos_gaussianReal` computes the cosine transform of a real Gaussian
  law.
* `TauCeti.Probability.integral_exp_mul_gaussianReal`, `integral_mul_exp_mul_gaussianReal` and
  `integrable_mul_exp_mul_gaussianReal` give the exponential and first tilted moments of a real
  Gaussian law.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, IMS Lecture Notes--Monograph
  Series 53.
-/

public section

noncomputable section

open MeasureTheory

namespace ProbabilityTheory

namespace IsGaussian

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
  [MeasurableSpace E] {μ : Measure E} [IsGaussian μ]

/-- An almost everywhere measurable continuous linear functional of a Gaussian measure has finite
exponential moments of every real order. -/
theorem integrableExpSet_dual (L : StrongDual ℝ E) (hL : AEMeasurable L μ := by fun_prop) :
    integrableExpSet L μ = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro t
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  refine (integrable_map_measure (f := L) (g := fun x : ℝ ↦ Real.exp (t * x))
    (by fun_prop) hL).mp ?_
  rw [IsGaussian.map_eq_gaussianReal L]
  exact integrable_exp_mul_gaussianReal t

/-- The moment-generating function of an almost everywhere measurable continuous linear functional
of a Gaussian measure is determined by its mean and variance. -/
theorem mgf_dual (L : StrongDual ℝ E) (t : ℝ) (hL : AEMeasurable L μ := by fun_prop) :
    mgf L μ t = Real.exp (t * μ[L] + t ^ 2 / 2 * Var[L; μ]) := by
  rw [← mgf_id_map hL, IsGaussian.map_eq_gaussianReal L, mgf_id_gaussianReal]
  rw [Real.coe_toNNReal _ (variance_nonneg _ _)]
  ring_nf

/-- The exponential moment of an almost everywhere measurable continuous linear functional of a
Gaussian measure as a nonnegative integral:
`∫⁻ exp (t L) dμ = exp (t μ[L] + t² / 2 · Var[L; μ])`. -/
theorem lintegral_ofReal_exp_mul_dual (L : StrongDual ℝ E) (t : ℝ)
    (hL : AEMeasurable L μ := by fun_prop) :
    ∫⁻ y, .ofReal (Real.exp (t * L y)) ∂μ =
      .ofReal (Real.exp (t * μ[L] + t ^ 2 / 2 * Var[L; μ])) := by
  have hint : t ∈ integrableExpSet L μ := by simp [integrableExpSet_dual L hL]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ (Real.exp_pos _).le),
    ← mgf_dual L t hL, mgf]

end IsGaussian

end ProbabilityTheory

open ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace TauCeti.Probability

/-- The exponential moment of a real Gaussian law: the integral form of
`ProbabilityTheory.mgf_fun_id_gaussianReal`. -/
theorem integral_exp_mul_gaussianReal (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂gaussianReal μ v = Real.exp (μ * t + v * t ^ 2 / 2) := by
  simpa only [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := μ) (v := v)) t

/-- A Gaussian exponential normalized by its cumulant-generating function has mean one. -/
theorem integral_exp_mul_sub_gaussianReal (μ b : ℝ) (v : ℝ≥0) :
    ∫ y, Real.exp (b * y - (μ * b + (v : ℝ) * b ^ 2 / 2)) ∂gaussianReal μ v = 1 := by
  simp_rw [Real.exp_sub, integral_div]
  rw [integral_exp_mul_gaussianReal, div_self (Real.exp_pos _).ne']

/-- The first exponentially tilted moment of a real Gaussian law:
`∫ x exp (t x) ∂N(μ, v) = (μ + v t) exp (μ t + v t² / 2)`, the derivative of its
moment-generating function. -/
theorem integral_mul_exp_mul_gaussianReal (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    ∫ x, x * Real.exp (t * x) ∂gaussianReal μ v =
      (μ + v * t) * Real.exp (μ * t + v * t ^ 2 / 2) := by
  have ht : t ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal μ v)) := by simp
  -- The tilted moment is the derivative at `t` of the moment-generating function.
  rw [← deriv_mgf ht, mgf_fun_id_gaussianReal]
  have hd : HasDerivAt (fun s : ℝ => μ * s + v * s ^ 2 / 2) (μ + v * t) t := by
    convert ((hasDerivAt_id' t).const_mul μ).add
      (((hasDerivAt_pow 2 t).const_mul (v : ℝ)).div_const 2) using 1
    ring
  rw [hd.exp.deriv, mul_comm]

/-- The first exponentially tilted moment of a real Gaussian law is integrable. -/
theorem integrable_mul_exp_mul_gaussianReal (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    Integrable (fun x : ℝ => x * Real.exp (t * x)) (gaussianReal μ v) := by
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (X := fun x : ℝ => x) (μ := gaussianReal μ v) (by simp) 1

/-- The sine at frequency `2π` is orthogonal under the standard Gaussian law to every
exponential with an integer exponent. -/
theorem integral_exp_int_mul_sin_gaussianReal (n : ℤ) :
    ∫ y, Real.exp ((n : ℝ) * y) * Real.sin (2 * Real.pi * y) ∂gaussianReal 0 1 = 0 := by
  -- The integrand is the imaginary part of `exp (z * y)` for `z = n + 2πi`.
  let z : ℂ := (n : ℝ) + (2 * Real.pi : ℝ) * Complex.I
  have hzint : Integrable (fun y : ℝ => Complex.exp (z * y)) (gaussianReal 0 1) :=
    integrable_cexp_mul_of_re_mem_integrableExpSet measurable_id.aemeasurable (by simp [z])
  calc
    _ = ∫ y, (Complex.exp (z * y)).im ∂gaussianReal 0 1 := by
      congr with y
      simp [Complex.exp_im, z]
    _ = (∫ y, Complex.exp (z * y) ∂gaussianReal 0 1).im := by
      simpa only [RCLike.im_to_complex] using integral_im hzint
    _ = (Complex.exp (z ^ 2 / 2)).im := by
      simpa [complexMGF] using
        congrArg Complex.im (complexMGF_id_gaussianReal (μ := 0) (v := 1) z)
    _ = 0 := by
      have him : (z ^ 2 / 2).im = n * (2 * Real.pi) := by
        simp [z, pow_two]
        ring
      rw [Complex.exp_im, him, Real.sin_periodic.int_mul_eq, Real.sin_zero, mul_zero]

/-- The cosine transform of the Gaussian law `gaussianReal μ v` is `exp (-v t² / 2) cos (t μ)`,
the real part of its characteristic function. -/
theorem integral_cos_gaussianReal (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    ∫ y, Real.cos (t * y) ∂gaussianReal μ v =
      Real.exp (-(v * t ^ 2) / 2) * Real.cos (t * μ) := by
  have hint : Integrable (fun y : ℝ => Complex.exp (t * y * Complex.I)) (gaussianReal μ v) :=
    .of_bound (by fun_prop) 1 (.of_forall fun y => by simp [Complex.norm_exp])
  calc
    _ = (∫ y, Complex.exp (t * y * Complex.I) ∂gaussianReal μ v).re := by
      rw [← RCLike.re_to_complex, ← integral_re hint]
      congr with y
      simp [Complex.exp_re]
    _ = _ := by
      rw [← charFun_apply_real, charFun_gaussianReal, Complex.exp_re]
      simp [← Complex.ofReal_pow, neg_div]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Every directional linear functional of a multivariate Gaussian has finite exponential moments
of all real orders.

This remains true for a covariance matrix that is not positive semidefinite: Mathlib then
totalizes the multivariate Gaussian to a Dirac measure at its mean. -/
theorem integrableExpSet_inner_multivariateGaussian (m θ : EuclideanSpace ℝ ι)
    (S : Matrix ι ι ℝ) :
    integrableExpSet (fun x ↦ ⟪θ, x⟫) (multivariateGaussian m S) = Set.univ := by
  simpa only [coe_innerSL_apply] using
    IsGaussian.integrableExpSet_dual (μ := multivariateGaussian m S) (innerSL ℝ θ)

/-- A real linear projection of a multivariate Gaussian has the corresponding directional mean
and covariance quadratic form as its scalar Gaussian parameters. -/
@[simp]
theorem map_inner_multivariateGaussian (m q : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) :
    (multivariateGaussian m S).map (fun x ↦ ⟪q, x⟫) =
      gaussianReal ⟪q, m⟫ (⟪q, S.toEuclideanLin q⟫).toNNReal := by
  have hmean : (∫ x, ⟪q, x⟫ ∂multivariateGaussian m S) = ⟪q, m⟫ := by
    simpa using (innerSL ℝ q).integral_comp_id_comm
      (IsGaussian.integrable_id (μ := multivariateGaussian m S))
  have hvar : Var[fun x ↦ ⟪q, x⟫; multivariateGaussian m S] =
      ⟪q, S.toEuclideanLin q⟫ := by
    rw [← covariance_self (by fun_prop),
      ← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
      covarianceBilin_multivariateGaussian hS]
    exact (Matrix.inner_toEuclideanCLM S q q).symm
  simpa only [coe_innerSL_apply, hmean, hvar] using
    (IsGaussian.map_eq_gaussianReal (μ := multivariateGaussian m S) (innerSL ℝ q))

/-- The moment-generating function of the inner product against a multivariate Gaussian vector.

The exponent consists of the directional mean and one half of the covariance quadratic form,
scaled respectively by `t` and `t²`. -/
theorem mgf_inner_multivariateGaussian (m θ : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (t : ℝ) :
    mgf (fun x ↦ ⟪θ, x⟫) (multivariateGaussian m S) t =
      Real.exp (t * ⟪θ, m⟫ + t ^ 2 / 2 * ⟪θ, S.toEuclideanLin θ⟫) := by
  have hnonneg : 0 ≤ ⟪θ, S.toEuclideanLin θ⟫ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct_comm] using hS.dotProduct_mulVec_nonneg θ.ofLp
  rw [← mgf_id_map (by fun_prop), map_inner_multivariateGaussian m θ hS,
    mgf_id_gaussianReal, Real.coe_toNNReal _ hnonneg]
  ring_nf

/-- The cumulant-generating function of an inner product against a multivariate Gaussian vector
is the quadratic polynomial determined by its directional mean and variance.

The formula holds for every real order, including for singular positive-semidefinite covariance
matrices. -/
@[simp]
theorem cgf_inner_multivariateGaussian (m θ : EuclideanSpace ℝ ι)
    {S : Matrix ι ι ℝ} (hS : S.PosSemidef) (t : ℝ) :
    cgf (fun x ↦ ⟪θ, x⟫) (multivariateGaussian m S) t =
      t * ⟪θ, m⟫ + t ^ 2 / 2 * ⟪θ, S.toEuclideanLin θ⟫ := by
  rw [cgf, mgf_inner_multivariateGaussian m θ hS t, Real.log_exp]

end TauCeti.Probability
