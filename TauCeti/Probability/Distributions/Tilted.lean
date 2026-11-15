/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Binomial
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Distributions.Gamma
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.MeasureTheory.Measure.Tilted

import TauCeti.MeasureTheory.Measure.Tilted
import TauCeti.Probability.Distributions.Binomial.Basic
import TauCeti.Probability.Distributions.Gamma.Basic
import TauCeti.Probability.Distributions.Poisson.Basic

/-!
# Exponential tilts of the Gaussian, gamma, Poisson, and binomial laws

When `exp (t * x)` is `μ`-integrable, tilting a law `μ` on `ℝ` or `ℕ` by `exp (t * x)` gives the
probability law with density `exp (t * x) / ∫ exp (t * y) ∂μ` with respect to `μ`; otherwise
`Measure.tilted` returns the zero measure. Each of the four families below is closed under this
operation, and the tilt acts on the parameters as follows.

* `TauCeti.Probability.gaussianReal_tilted_mul`: the Gaussian `N(m, v)` tilts to
  `N(m + v t, v)`, including the point mass at variance zero, with the pointwise density identity
  `TauCeti.Probability.gaussianPDFReal_mul_exp_div_mgf`, and
  `TauCeti.Probability.setIntegral_exp_mul_gaussianReal` reads this off as a weighted set
  integral;
* `TauCeti.Probability.gammaMeasure_tilted_mul`: the gamma law of shape `a` and rate `r` tilts
  to rate `r - t`, for `t < r`, which is exactly the range where the tilt is a probability law;
* `TauCeti.Probability.poissonMeasure_tilted_mul`: the native Poisson law of rate `r` tilts to
  rate `r * exp t`, including the point mass at rate zero;
* `TauCeti.Probability.binomial_tilted_mul`: the native binomial law with success probability `p`
  tilts to success probability `p * exp t / (1 - p + p * exp t)`, including the point masses at
  `p = 0` and `p = 1`.

The continuous identities compare densities through `TauCeti.tilted_withDensity`, and the discrete
ones compare singleton masses through `TauCeti.tilted_singleton`; in each case the normalizing
constant is the family's known moment-generating function.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, Vol. 1,
  2nd ed., Wiley, 1994.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005.
-/

public section

open MeasureTheory ProbabilityTheory Real

open scoped ENNReal NNReal unitInterval

namespace TauCeti.Probability

/-- Multiplying the Gaussian density of `N(m, v)` by `exp (t * x)` divided by the
moment-generating function `exp (m t + v t² / 2)` gives the density of `N(m + v t, v)`. At variance
zero both densities vanish. -/
theorem gaussianPDFReal_mul_exp_div_mgf (m : ℝ) (v : ℝ≥0) (t x : ℝ) :
    gaussianPDFReal m v x * (exp (t * x) / exp (m * t + v * t ^ 2 / 2)) =
      gaussianPDFReal (m + v * t) v x := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal]
  simp only [gaussianPDFReal, mul_assoc, ← exp_add, ← exp_sub]
  congr 2
  field_simp
  ring

/-- **Exponential tilting of a Gaussian law shifts its mean.** Tilting `N(m, v)` by
`exp (t * x)` gives `N(m + v t, v)`; at variance zero both sides are the point mass at `m`. -/
@[simp]
theorem gaussianReal_tilted_mul (m : ℝ) (v : ℝ≥0) (t : ℝ) :
    (gaussianReal m v).tilted (t * ·) = gaussianReal (m + v * t) v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  have hZ : ∫ x, exp (t * x) ∂gaussianReal m v = exp (m * t + v * t ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := m) (v := v)) t
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    tilted_withDensity (measurable_gaussianPDF _ _).aemeasurable (by fun_prop),
    ← gaussianReal_of_var_ne_zero _ hv, hZ]
  congr with x
  rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    gaussianPDFReal_mul_exp_div_mgf]

/-- Integrating the exponential weight `exp (t * x)` against `N(m, v)` over a set `s` gives the
moment-generating function `exp (m t + v t² / 2)` times the mass of `s` under the tilted law
`N(m + v t, v)`. -/
theorem setIntegral_exp_mul_gaussianReal (m : ℝ) (v : ℝ≥0) (t : ℝ) (s : Set ℝ) :
    ∫ x in s, exp (t * x) ∂gaussianReal m v =
      exp (m * t + v * t ^ 2 / 2) * (gaussianReal (m + v * t) v).real s := by
  have hZ : ∫ x, exp (t * x) ∂gaussianReal m v = exp (m * t + v * t ^ 2 / 2) := by
    simpa [mgf] using congrFun (mgf_id_gaussianReal (μ := m) (v := v)) t
  have h := setIntegral_tilted (μ := gaussianReal m v) (t * ·) (fun _ => (1 : ℝ)) s
  rw [gaussianReal_tilted_mul, hZ, setIntegral_const] at h
  simp only [smul_eq_mul, mul_one, integral_div] at h
  rw [h]
  field_simp

/-- **Exponential tilting of a gamma law lowers its rate.** For `t < r`, tilting the gamma law of
shape `a` and rate `r` by `exp (t * x)` gives the gamma law of shape `a` and rate `r - t`. -/
theorem gammaMeasure_tilted_mul {a r t : ℝ} (ha : 0 < a) (hr : 0 < r) (ht : t < r) :
    (gammaMeasure a r).tilted (t * ·) = gammaMeasure a (r - t) := by
  have hZ : ∫ x, exp (t * x) ∂gammaMeasure a r = (1 - t / r) ^ (-a) := by
    simpa [mgf] using mgf_id_gammaMeasure ha hr ht
  rw [gammaMeasure, tilted_withDensity (g := gammaPDF a r)
    (measurable_gammaPDFReal a r).ennreal_ofReal.aemeasurable (by fun_prop), ← gammaMeasure, hZ,
    gammaMeasure]
  congr with x
  rw [gammaPDF, gammaPDF, ← ENNReal.ofReal_mul (gammaPDFReal_nonneg ha hr _)]
  congr 1
  rcases lt_or_ge x 0 with hx | hx
  · simp [gammaPDFReal, hx.not_ge]
  have hrt : r * (1 - t / r) = r - t := by field_simp
  have h1 : 0 < 1 - t / r := by rwa [sub_pos, div_lt_one hr]
  simp only [gammaPDFReal, hx, ↓reduceIte]
  rw [rpow_neg h1.le, div_inv_eq_mul, ← hrt, mul_rpow hr.le h1.le]
  rw [show -((r * (1 - t / r)) * x) = -(r * x) + t * x by field_simp; ring, exp_add]
  ring

/-- **Exponential tilting of a Poisson law scales its rate.** Tilting the native Poisson law of
rate `r` by `exp (t * n)` gives the Poisson law of rate `r * exp t`; at rate zero both sides are the
point mass at `0`. -/
@[simp]
theorem poissonMeasure_tilted_mul (r : ℝ≥0) (t : ℝ) :
    (poissonMeasure r).tilted (fun n ↦ t * n) = poissonMeasure (r * (exp t).toNNReal) := by
  have hZ : ∫ n, exp (t * n) ∂poissonMeasure r = exp (r * (exp t - 1)) := by
    simp [← pgf_poissonMeasure, pgf_exp, mgf]
  refine Measure.ext_of_singleton fun n ↦ ?_
  rw [tilted_singleton, hZ, poissonMeasure_singleton, poissonMeasure_singleton,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rw [NNReal.coe_mul, Real.coe_toNNReal _ (exp_pos t).le, mul_pow, ← exp_nat_mul]
  rw [show -(r * exp t : ℝ) = -r - r * (exp t - 1) by ring, exp_sub, mul_comm (n : ℝ) t]
  field_simp

/-- **Exponential tilting of a binomial law.** Tilting the native binomial law with `n` trials and
success probability `p` by `exp (t * k)` gives the binomial law with `n` trials and success
probability `q = p * exp t / (1 - p + p * exp t)`. The boundary cases `p = 0` and `p = 1` are
included, where `q = p`. -/
theorem binomial_tilted_mul (n : ℕ) (p : I) (t : ℝ) {q : I}
    (hq : (q : ℝ) = p * exp t / (1 - p + p * exp t)) :
    (binomial n p).tilted (fun k ↦ t * k) = binomial n q := by
  have hD : 0 < 1 - (p : ℝ) + p * exp t := by
    rcases p.2.1.eq_or_lt with hp | hp
    · simp [← hp]
    · linarith [p.2.2, mul_pos hp (exp_pos t)]
  have hZ : ∫ k, exp (t * k) ∂binomial n p = (1 - p + p * exp t) ^ n := by
    simp [← pgf_binomial, pgf_exp, mgf]
  have hq' : 1 - (q : ℝ) = (1 - p) / (1 - p + p * exp t) := by
    rw [hq]
    field_simp
    ring
  refine Measure.ext_of_singleton fun k ↦ ?_
  rw [tilted_singleton, hZ, binomial_singleton, binomial_singleton,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  rcases lt_or_ge n k with hk | hk
  · simp [Nat.choose_eq_zero_of_lt hk]
  rw [hq', hq, div_pow, div_pow, mul_comm t, exp_nat_mul,
    show n = k + (n - k) by omega, pow_add, Nat.add_sub_cancel_left]
  field_simp
  ring

end TauCeti.Probability
