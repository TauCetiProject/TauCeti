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
import TauCeti.Probability.Moments.Basic

/-!
# Moment- and cumulant-generating functions of Gaussian linear functionals

This file proves that every almost everywhere measurable continuous linear functional of a
Gaussian measure has finite exponential moments of every real order and computes its
moment-generating function. It then specializes the general result to inner products against a
multivariate Gaussian vector, expressing the variance as the covariance-matrix quadratic form,
and computes the corresponding cumulant-generating function. It also computes the
moment-generating function of a linear combination of independent real Gaussian variables, in
particular of a linear form `y ⬝ᵥ g` of a vector `g` with independent Gaussian coordinates; this
is the auxiliary Gaussian integral in the decoupling proof of the Hanson–Wright inequality.

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
* `ProbabilityTheory.iIndepFun.mgf_sum_mul_gaussianReal` computes the moment-generating function
  of `∑ i ∈ s, y i * X i` for independent real Gaussian variables `X i`, and
  `TauCeti.Probability.mgf_dotProduct_pi_gaussianReal` specializes it to a linear form under a
  finite product of real Gaussian laws.
* `TauCeti.Probability.integrable_exp_mul_sum_mul_gaussianReal` says that such a linear
  combination has finite exponential moments of every order, even without independence.
* `TauCeti.Probability.integral_exp_int_mul_sin_gaussianReal` shows that the sine at frequency
  `2π` is orthogonal to every integer-exponent exponential under the standard Gaussian law.
* `TauCeti.Probability.integral_cos_gaussianReal` computes the cosine transform of a real Gaussian
  law.
* `TauCeti.Probability.gaussian_exp_integral`, `gaussian_x_exp_integral` and
  `gaussian_x_exp_integrable` give the exponential and first tilted moments of the standard
  Gaussian law.

## References

* M. L. Eaton, *Multivariate Statistics: A Vector Space Approach*, IMS Lecture Notes--Monograph
  Series 53.
-/

public section

noncomputable section

open MeasureTheory
open scoped NNReal

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

namespace iIndepFun

variable {Ω γ : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : γ → Ω → ℝ}
  {μ : γ → ℝ} {v : γ → ℝ≥0}

/-- The moment-generating function of a linear combination `∑ i ∈ s, y i * X i` of independent
real Gaussian variables `X i ∼ N(μ i, v i)` is that of the Gaussian law with mean
`∑ i ∈ s, y i * μ i` and variance `∑ i ∈ s, v i * y i ^ 2`. Only the variables indexed by `s`
need be independent and Gaussian. -/
theorem mgf_sum_mul_gaussianReal {s : Finset γ} (hInd : iIndepFun (s.restrict X) P)
    (hLaw : ∀ i ∈ s, HasLaw (X i) (gaussianReal (μ i) (v i)) P) (y : γ → ℝ) (r : ℝ) :
    mgf (fun ω ↦ ∑ i ∈ s, y i * X i ω) P r =
      Real.exp (r * ∑ i ∈ s, y i * μ i + r ^ 2 / 2 * ∑ i ∈ s, (v i : ℝ) * y i ^ 2) := by
  -- The scaled variables are still independent, so the mgf factors over the summands.
  have h := (hInd.comp (fun i x ↦ y i * x) fun i ↦ measurable_const_mul (y i)).mgf_sum₀
    (fun i ↦ (hLaw i i.property).aemeasurable.const_mul (y i)) Finset.univ (t := r)
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Real.exp_sum,
    ← Finset.prod_coe_sort s]
  convert h using 1
  · congr 1
    ext ω
    simp [Function.comp_def, Finset.restrict, Finset.sum_attach s fun i ↦ y i * X i ω]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Function.comp_def, mgf_const_mul, Finset.restrict, mgf_gaussianReal (hLaw i i.property)]
  ring_nf

end iIndepFun

end ProbabilityTheory

open ProbabilityTheory
open scoped RealInnerProductSpace

namespace TauCeti.Probability

/-- The exponential moment of the standard Gaussian. -/
theorem gaussian_exp_integral (a : ℝ) :
    ∫ x : ℝ, Real.exp (a * x) ∂ProbabilityTheory.gaussianReal 0 1 = Real.exp (a ^ 2 / 2) := by
  have h := congrFun (ProbabilityTheory.mgf_fun_id_gaussianReal (μ := 0) (v := 1)) a
  simpa [ProbabilityTheory.mgf] using h

/-- A Gaussian exponential normalized by its cumulant-generating function has mean one. -/
theorem integral_exp_mul_sub_gaussianReal (μ b : ℝ) (v : ℝ≥0) :
    ∫ y, Real.exp (b * y - (μ * b + (v : ℝ) * b ^ 2 / 2)) ∂gaussianReal μ v = 1 := by
  simp_rw [Real.exp_sub, integral_div]
  have h : (∫ y, Real.exp (b * y) ∂gaussianReal μ v) =
      Real.exp (μ * b + (v : ℝ) * b ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := μ) (v := v)) b
  rw [h, div_self (ne_of_gt (Real.exp_pos _))]

/-- The first exponentially tilted moment of the standard Gaussian. -/
theorem gaussian_x_exp_integral (a : ℝ) :
    ∫ x : ℝ, x * Real.exp (a * x) ∂ProbabilityTheory.gaussianReal 0 1 =
      a * Real.exp (a ^ 2 / 2) := by
  have ha : a ∈ interior (integrableExpSet (fun x : ℝ => x) (gaussianReal 0 1)) := by simp
  -- The tilted moment is the derivative at `a` of the moment-generating function.
  rw [← deriv_mgf ha, mgf_fun_id_gaussianReal]
  have hd : HasDerivAt (fun t : ℝ => Real.exp (0 * t + (1 : ℝ≥0) * t ^ 2 / 2))
      (a * Real.exp (a ^ 2 / 2)) a := by
    convert ((hasDerivAt_id a).pow 2 |>.div_const 2).exp using 1 <;> simp; ring
  exact hd.deriv

/-- The first exponentially tilted moment of the standard Gaussian is integrable. -/
theorem gaussian_x_exp_integrable (a : ℝ) :
    Integrable (fun x : ℝ => x * Real.exp (a * x)) (gaussianReal 0 1) := by
  simpa using integrable_pow_mul_exp_of_mem_interior_integrableExpSet
    (X := fun x : ℝ => x) (μ := gaussianReal 0 1) (by simp) 1

/-- A linear combination `∑ i ∈ s, y i * X i` of real Gaussian variables `X i` has finite
exponential moments of every real order `r`: the function `ω ↦ exp (r * ∑ i ∈ s, y i * X i ω)` is
integrable. The variables need not be independent, and only those indexed by `s` need be Gaussian.
The measure need be finite only for the empty sum, whose integrand is the constant `1`; otherwise
the law of any summand makes it a probability measure. -/
theorem integrable_exp_mul_sum_mul_gaussianReal {Ω γ : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} {X : γ → Ω → ℝ} {μ : γ → ℝ} {v : γ → ℝ≥0}
    (s : Finset γ) (hfinite : s = ∅ → IsFiniteMeasure P)
    (hLaw : ∀ i ∈ s, HasLaw (X i) (gaussianReal (μ i) (v i)) P) (y : γ → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ Real.exp (r * ∑ i ∈ s, y i * X i ω)) P := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · have := hfinite rfl
    simp
  -- Hölder's inequality with every exponent equal to the number of summands.
  have hcard : (0 : ℝ) < s.card := mod_cast hs.card_pos
  refine integrable_exp_mul_sum_of_integrable_exp_mul (p := fun _ ↦ (s.card : ℝ))
    (fun _ _ ↦ hcard) (by simp [hcard.ne']) fun i hi ↦ ?_
  simpa only [mul_assoc] using (hLaw i hi).integrable_fun_comp
    (integrable_exp_mul_gaussianReal (s.card * r * y i))

/-- The moment-generating function of a linear form `g ↦ y ⬝ᵥ g` under a finite product of
real Gaussian laws `gaussianReal (μ l) (v l)`, that is, for a vector of independent Gaussian
coordinates. -/
theorem mgf_dotProduct_pi_gaussianReal {γ : Type*} [Fintype γ] (y μ : γ → ℝ) (v : γ → ℝ≥0)
    (r : ℝ) :
    mgf (fun g : γ → ℝ ↦ y ⬝ᵥ g) (Measure.pi fun l ↦ gaussianReal (μ l) (v l)) r =
      Real.exp (r * (y ⬝ᵥ μ) + r ^ 2 / 2 * ∑ l, (v l : ℝ) * y l ^ 2) := by
  -- The coordinate projections are independent, with the factor laws as their laws.
  have hInd : iIndepFun (fun l (g : γ → ℝ) ↦ g l) (Measure.pi fun l ↦ gaussianReal (μ l) (v l)) :=
    iIndepFun_pi fun _ ↦ aemeasurable_id
  simpa only [dotProduct] using (hInd.restrict Finset.univ).mgf_sum_mul_gaussianReal
    (fun l _ ↦ (measurePreserving_eval (fun l ↦ gaussianReal (μ l) (v l)) l).hasLaw) y r

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
