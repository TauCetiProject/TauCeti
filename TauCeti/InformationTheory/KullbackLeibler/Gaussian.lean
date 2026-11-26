/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Distributions.Gaussian.Real

import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import TauCeti.InformationTheory.KullbackLeibler.Basic
import TauCeti.InformationTheory.KullbackLeibler.ChangeOfReference
import TauCeti.InformationTheory.KullbackLeibler.Pi
import TauCeti.Probability.Distributions.Gaussian.Affine
import TauCeti.Probability.Distributions.Gaussian.Density
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PDF

/-!
# Relative entropy between Gaussian laws

For variances `u, v ≠ 0`, the relative entropy `klDiv (gaussianReal a u) (gaussianReal b v)` is
`(u / v - 1 - log (u / v)) / 2 + (a - b) ^ 2 / (2 v)`.
The first summand compares the variances and vanishes exactly when `u = v`, since
`log x ≤ x - 1`; the second compares the means on the scale of the reference variance `v`.

Both laws have positive densities with respect to Lebesgue measure, so their log-likelihood ratio
is, almost everywhere, the difference of the logarithms of the two densities
(`TauCeti.llr_add_llr`). This difference is a quadratic polynomial in `x`, and its mean under
`N(a, u)` follows from the first two centred moments of `N(a, u)`.

On Euclidean space, the isotropic Gaussian laws `N(a, u • 1)` and `N(b, v • 1)` are products of
real Gaussian laws of variances `u` and `v`, transported along `WithLp.toLp 2`
(`TauCeti.Probability.multivariateGaussian_smul_one_eq_map_pi`). Relative entropy is invariant
under that measurable equivalence and tensorizes over finite products (`TauCeti.klDiv_pi`), so the
divergence is the sum of the coordinate divergences,
`d / 2 * (u / v - 1 - log (u / v)) + ‖a - b‖ ^ 2 / (2 v)` in dimension `d`.

When one of the two laws is a point mass, the Gaussian law with zero covariance, and the other
has positive definite covariance, the divergence is infinite in positive dimension: the
nondegenerate law charges no point, while the point mass is carried by one.

## Main statements

* `Real.klDiv_gaussianReal_gaussianReal`: the relative entropy between real Gaussian laws.
* `Real.klDiv_gaussianReal`: its case of a common variance.
* `TauCeti.klDiv_multivariateGaussian_smul_one`: the relative entropy between isotropic Gaussian
  laws on Euclidean space.
* `TauCeti.klDiv_multivariateGaussian`: its case of a common variance.
* `TauCeti.klDiv_multivariateGaussian_dirac`, `TauCeti.klDiv_dirac_multivariateGaussian`: the
  relative entropy between a nondegenerate Gaussian law and a point mass, in either order, is
  infinite.

## References

* S. Kullback, *Information Theory and Statistics*, Wiley, 1959, Chapter 9, for the divergence
  between multivariate normal laws.
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer, 2009, Corollary 2.1(i),
  p. 87, for unit variance.

The common-variance statements `Real.klDiv_gaussianReal` and `TauCeti.klDiv_multivariateGaussian`,
and the reduction of the isotropic case to its coordinates by tensorization, are adapted from the
lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Nonparametric/LowerBounds/Gaussian.lean`, theorems `CKSD.klDiv_gaussianReal_gaussianReal`
(common variance, by exponential tilting) and `CKSD.klDiv_pi_gaussianReal`. The formula for
different variances and its density-based proof on the real line are not drawn from it.
-/

public section

open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal NNReal

namespace TauCeti

/-- Under `N(a, u)` with `u ≠ 0`, the log-likelihood ratio against `N(b, v)` with `v ≠ 0` is
almost everywhere the difference of the logarithms of the two densities. -/
private theorem llr_gaussianReal_ae_eq (a b : ℝ) {u v : ℝ≥0} (hu : u ≠ 0) (hv : v ≠ 0) :
    llr (gaussianReal a u) (gaussianReal b v) =ᵐ[gaussianReal a u]
      fun x ↦ log (gaussianPDFReal a u x) - log (gaussianPDFReal b v x) := by
  have hμ := gaussianReal_absolutelyContinuous a hu
  have hdens (m : ℝ) (w : ℝ≥0) :
      llr (gaussianReal m w) volume =ᵐ[volume] fun x ↦ log (gaussianPDFReal m w x) := by
    filter_upwards [rnDeriv_gaussianReal m w] with x hx
    simp [llr_def, hx, gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg m w x)]
  filter_upwards [llr_add_llr (hμ.trans (gaussianReal_absolutelyContinuous' b hv)) hμ,
    hμ.ae_le (hdens a u), hμ.ae_le (hdens b v)] with x hx hxa hxb
  rw [← hxa, ← hxb, ← hx, Pi.add_apply, add_sub_cancel_right]

/-- **Relative entropy between real Gaussian laws.** For variances `u, v ≠ 0`,
`klDiv N(a, u) N(b, v) = (u / v - 1 - log (u / v)) / 2 + (a - b) ^ 2 / (2 v)`. -/
theorem _root_.Real.klDiv_gaussianReal_gaussianReal (a b : ℝ) {u v : ℝ≥0} (hu : u ≠ 0)
    (hv : v ≠ 0) :
    klDiv (gaussianReal a u) (gaussianReal b v) =
      ENNReal.ofReal ((u / v - 1 - log (u / v)) / 2 + (a - b) ^ 2 / (2 * v)) := by
  set μ := gaussianReal a u
  have huR : (0 : ℝ) < u := by positivity
  have hvR : (0 : ℝ) < v := by positivity
  have hμν : μ ≪ gaussianReal b v :=
    (gaussianReal_absolutelyContinuous a hu).trans (gaussianReal_absolutelyContinuous' b hv)
  -- The log-likelihood ratio is a quadratic polynomial in the centred variable `x - a`.
  set c₁ : ℝ := (a - b) / v
  set c₂ : ℝ := 1 / (2 * v) - 1 / (2 * u)
  set K : ℝ := (log v - log u) / 2 + (a - b) ^ 2 / (2 * v)
  have hpoly : (fun x ↦ log (gaussianPDFReal a u x) - log (gaussianPDFReal b v x)) =
      fun x ↦ c₂ * (x - a) ^ 2 + (c₁ * (x - a) + K) := by
    ext x
    simp only [Probability.log_gaussianPDFReal, log_mul (by positivity : (2 * π : ℝ) ≠ 0) huR.ne',
      log_mul (by positivity : (2 * π : ℝ) ≠ 0) hvR.ne', c₁, c₂, K]
    field_simp
    ring
  have hllr := (llr_gaussianReal_ae_eq a b hu hv).trans (Filter.EventuallyEq.of_eq hpoly)
  have hmem : MemLp (fun x ↦ x - a) 2 μ := (memLp_id_gaussianReal 2).sub (memLp_const a)
  have hsq : Integrable (fun x ↦ c₂ * (x - a) ^ 2) μ := hmem.integrable_sq.const_mul c₂
  have hlin : Integrable (fun x ↦ c₁ * (x - a)) μ :=
    (hmem.integrable one_le_two).const_mul c₁
  have hlinK : Integrable (fun x ↦ c₁ * (x - a) + K) μ := hlin.add (integrable_const K)
  have hint : Integrable (llr μ (gaussianReal b v)) μ :=
    (integrable_congr hllr).2 (hsq.add hlinK)
  -- The centred moments of `N(a, u)` are `∫ (x - a) = 0` and `∫ (x - a) ^ 2 = u`.
  have hm₁ : ∫ x, (x - a) ∂μ = 0 := by
    simpa using Probability.integral_sub_pow_two_mul_add_one_gaussianReal a u 0
  have hm₂ : ∫ x, (x - a) ^ 2 ∂μ = u := by
    simpa using Probability.integral_sub_pow_two_mul_gaussianReal a u 1
  rw [klDiv_of_ac_of_integrable hμν hint, integral_congr_ae hllr, integral_add hsq hlinK,
    integral_add hlin (integrable_const K), integral_const_mul, integral_const_mul, hm₁, hm₂]
  simp only [probReal_univ, integral_const, smul_eq_mul, one_mul, c₁, c₂, K]
  congr 1
  rw [log_div huR.ne' hvR.ne']
  field_simp
  ring

/-- The relative entropy between real Gaussian laws with a common nonzero variance `v` is
`(a - b) ^ 2 / (2 v)`. -/
theorem _root_.Real.klDiv_gaussianReal (a b : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    klDiv (gaussianReal a v) (gaussianReal b v) = ENNReal.ofReal ((a - b) ^ 2 / (2 * v)) := by
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  simpa [hvR] using Real.klDiv_gaussianReal_gaussianReal a b hv hv

/-- **Relative entropy between isotropic Gaussian laws.** On `EuclideanSpace ℝ ι`, for variances
`u, v > 0`, `klDiv N(a, u • 1) N(b, v • 1)` is
`card ι / 2 * (u / v - 1 - log (u / v)) + ‖a - b‖ ^ 2 / (2 v)`. -/
theorem klDiv_multivariateGaussian_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : EuclideanSpace ℝ ι) {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    klDiv (multivariateGaussian a (u • 1)) (multivariateGaussian b (v • 1)) =
      ENNReal.ofReal
        (Fintype.card ι / 2 * (u / v - 1 - log (u / v)) + ‖a - b‖ ^ 2 / (2 * v)) := by
  lift u to ℝ≥0 using hu.le
  lift v to ℝ≥0 using hv.le
  have hu0 : u ≠ 0 := by exact_mod_cast hu.ne'
  have hv0 : v ≠ 0 := by exact_mod_cast hv.ne'
  -- Each coordinate term is nonnegative, by `log x ≤ x - 1`.
  have hlog : 0 ≤ (u : ℝ) / v - 1 - log ((u : ℝ) / v) := by
    linarith [log_le_sub_one_of_pos (show (0 : ℝ) < u / v by positivity)]
  rw [Probability.multivariateGaussian_smul_one_eq_map_pi,
    Probability.multivariateGaussian_smul_one_eq_map_pi, ← MeasurableEquiv.coe_toLp,
    Measure.klDiv_map_measurableEquiv, klDiv_pi]
  simp_rw [Real.klDiv_gaussianReal_gaussianReal _ _ hu0 hv0]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ by positivity, Finset.sum_add_distrib,
    EuclideanSpace.real_norm_sq_eq, Finset.sum_div]
  simp only [PiLp.sub_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  ring

/-- The relative entropy between isotropic Gaussian laws on Euclidean space with a common
positive variance `v` is `‖a - b‖ ^ 2 / (2 v)`. -/
theorem klDiv_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : EuclideanSpace ℝ ι) {v : ℝ} (hv : 0 < v) :
    klDiv (multivariateGaussian a (v • 1)) (multivariateGaussian b (v • 1)) =
      ENNReal.ofReal (‖a - b‖ ^ 2 / (2 * v)) := by
  simpa [hv.ne'] using klDiv_multivariateGaussian_smul_one a b hv hv

/-- In positive dimension, the relative entropy of a Gaussian law with positive definite
covariance with respect to a point mass is infinite. The point mass `dirac b` is the Gaussian law
`multivariateGaussian b 0` with zero covariance. -/
theorem klDiv_multivariateGaussian_dirac {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a b : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    klDiv (multivariateGaussian a S) (Measure.dirac b) = ∞ := by
  refine klDiv_of_not_ac fun h ↦ ?_
  have hcompl : multivariateGaussian a S {b}ᶜ = 0 :=
    h (by simp [Measure.dirac_apply' _ (measurableSet_singleton b).compl])
  rw [prob_compl_eq_one_sub (measurableSet_singleton b),
    Probability.multivariateGaussian_absolutelyContinuous hS a (measure_singleton b),
    tsub_zero] at hcompl
  exact one_ne_zero hcompl

/-- In positive dimension, the relative entropy of a point mass with respect to a Gaussian law
with positive definite covariance is infinite. -/
theorem klDiv_dirac_multivariateGaussian {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a b : EuclideanSpace ℝ ι) {S : Matrix ι ι ℝ} (hS : S.PosDef) :
    klDiv (Measure.dirac a) (multivariateGaussian b S) = ∞ := by
  refine klDiv_of_not_ac fun h ↦ ?_
  have ha := h <|
    Probability.multivariateGaussian_absolutelyContinuous hS b (measure_singleton a)
  simp at ha

end TauCeti
