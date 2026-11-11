/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.ProperComplex.Affine
public import TauCeti.Probability.Distributions.NoncentralChi.Gaussian

/-!
# Rice moduli of proper complex Gaussian coordinates

The modulus of a proper complex Gaussian coordinate of mean `m` and positive complex variance
`v` has Rice law: the noncentral chi law of degree two, coordinate scale `s = √(v / 2)`, and
noncentrality `‖m‖ / s`. The factor one half comes from the real and imaginary variances.
The joint real-coordinate law makes this identification valid for a coordinate of any proper
complex Gaussian vector with positive semidefinite covariance, including singular vectors.
At zero coordinate variance the modulus is instead the point mass at `‖m‖`.

The Rice density is available as `noncentralChiPDFReal_two_div_scale_eq_besselI` in
`TauCeti.Probability.Distributions.NoncentralChi.PDF`. The measure identity here allows the
density, cdf, moment, and quantile theory of noncentral chi laws to be applied directly, without
a separate Rice-family definition.

The proof uses the planar coordinate marginal theorem
`map_finTwo_re_im_eval_properComplexGaussianMeasure` and the spherical Gaussian norm identity
`map_norm_multivariateGaussian_noncentral_of_scale`.

## References

* D. Tse and P. Viswanath, *Fundamentals of Wireless Communication*, Cambridge University
  Press, 2005, appendix A.
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ComplexOrder NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive-variance proper complex Gaussian coordinate has Rice modulus: a noncentral chi
law of degree two, scale `√((C i i).re / 2)`, and noncentrality
`‖m i‖ / √((C i i).re / 2)`. -/
@[simp]
theorem map_norm_eval_properComplexGaussianMeasure (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (hC : C.PosSemidef) (i : ι) (hi : 0 < (C i i).re) :
    (properComplexGaussianMeasure m C).map (fun z ↦ ‖z i‖) =
      noncentralChiMeasure 2 (‖m i‖₊ / (Real.sqrt ((C i i).re / 2)).toNNReal)
        (Real.sqrt ((C i i).re / 2)) := by
  have hs : 0 < Real.sqrt ((C i i).re / 2) := Real.sqrt_pos.2 (by positivity)
  have hnorm (z : ℂ) : ‖(WithLp.toLp 2 ![z.re, z.im] : EuclideanSpace ℝ (Fin 2))‖ = ‖z‖ := by
    rw [← Complex.orthonormalBasisOneI_repr_apply, WithLp.toLp_ofLp]
    exact Complex.orthonormalBasisOneI.repr.norm_map z
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) ↦ μ.map (fun x ↦ ‖x‖))
    (map_finTwo_re_im_eval_properComplexGaussianMeasure m hC i)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  have hgauss := map_norm_multivariateGaussian_noncentral_of_scale
    (WithLp.toLp 2 ![(m i).re, (m i).im]) hs
  rw [Real.sq_sqrt (by positivity)] at hgauss
  rw [hgauss] at h
  have hnnorm : ‖(WithLp.toLp 2 ![(m i).re, (m i).im] : EuclideanSpace ℝ (Fin 2))‖₊ =
      ‖m i‖₊ := NNReal.eq (hnorm (m i))
  simpa [Function.comp_def, hnorm, hnnorm] using h

/-- At zero complex coordinate variance, the modulus is the point mass at the norm of the
mean, even when other coordinates have nonzero variance or the covariance is invalid. -/
@[simp]
theorem map_norm_eval_properComplexGaussianMeasure_of_variance_zero (m : ι → ℂ)
    {C : Matrix ι ι ℂ} (i : ι) (hi : (C i i).re = 0) :
    (properComplexGaussianMeasure m C).map (fun z ↦ ‖z i‖) = Measure.dirac ‖m i‖ := by
  by_cases hC : C.PosSemidef
  swap
  · simp [properComplexGaussianMeasure_of_not_posSemidef m hC]
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 2)) ↦ μ.map (fun x ↦ ‖x‖))
    (map_finTwo_re_im_eval_properComplexGaussianMeasure m hC i)
  rw [Measure.map_map (by fun_prop) (by fun_prop)] at h
  simpa [hi, Function.comp_def, ← Complex.orthonormalBasisOneI_repr_apply] using h

end TauCeti.Probability

namespace ProbabilityTheory

open TauCeti.Probability

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
  {P : Measure Ω} {Z : Ω → ι → ℂ} {m : ι → ℂ} {C : Matrix ι ι ℂ}

/-- The modulus of a positive-variance proper complex Gaussian coordinate has Rice law. -/
theorem HasLaw.norm_eval_properComplexGaussianMeasure
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (hC : C.PosSemidef) (i : ι)
    (hi : 0 < (C i i).re) :
    HasLaw (fun ω ↦ ‖Z ω i‖)
      (noncentralChiMeasure 2 (‖m i‖₊ / (Real.sqrt ((C i i).re / 2)).toNNReal)
        (Real.sqrt ((C i i).re / 2))) P :=
  (HasLaw.mk (by fun_prop : Measurable (fun z : ι → ℂ ↦ ‖z i‖)).aemeasurable
    (map_norm_eval_properComplexGaussianMeasure m hC i hi)).fun_comp hZ

/-- A zero-variance proper complex Gaussian coordinate has deterministic modulus. -/
theorem HasLaw.norm_eval_properComplexGaussianMeasure_of_variance_zero
    (hZ : HasLaw Z (properComplexGaussianMeasure m C) P) (i : ι)
    (hi : (C i i).re = 0) :
    HasLaw (fun ω ↦ ‖Z ω i‖) (Measure.dirac ‖m i‖) P :=
  (HasLaw.mk (by fun_prop : Measurable (fun z : ι → ℂ ↦ ‖z i‖)).aemeasurable
    (map_norm_eval_properComplexGaussianMeasure_of_variance_zero m i hi)).fun_comp hZ

end ProbabilityTheory
