/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Analysis.SpecialFunctions.Erf.Inequalities

/-!
# Tail bounds for the standard Gaussian law

Write `Φ = cdf (gaussianReal 0 1)` for the standard Gaussian distribution function and
`φ = gaussianPDFReal 0 1` for its density. This file proves the two classical upper bounds on the
upper tail `1 − Φ(r)`, the measure of the half-line `(r, ∞)`:

* `1 − Φ(r) < φ(r)/r` for every `r > 0`;
* `1 − Φ(r) ≤ e^{−r²/2}/2` for every `r ≥ 0`, strictly for `r > 0`. At `r = 0` both sides
  are `1/2`, so the constant `1/2` is optimal.

Since a half-space at distance `r` from the origin has standard Gaussian measure `1 − Φ(r)`, they
bound the Gaussian measure of half-spaces far from the origin. The second bound sharpens by the
factor `1/2` the classical estimate `1 − Φ(r) ≤ e^{−r²/2}`.

## Main results

* `TauCeti.Probability.one_sub_cdf_gaussianReal_lt_gaussianPDFReal_div`: `1 − Φ(r) < φ(r)/r`
  for `r > 0`.
* `TauCeti.Probability.one_sub_cdf_gaussianReal_le_exp_div_two`: `1 − Φ(r) ≤ e^{−r²/2}/2` for
  `r ≥ 0`.
* `TauCeti.Probability.one_sub_cdf_gaussianReal_lt_exp_div_two`: `1 − Φ(r) < e^{−r²/2}/2` for
  `r > 0`.

## Implementation notes

With `x = r/√2`, the upper tail is `1 − Φ(r) = erfc(x)/2`, so the bounds are the bounds
`erfc x < e^{−x²}/(√π x)` and `erfc x ≤ e^{−x²}` of `TauCeti.Real.erfc_lt_exp_neg_sq_div` and
`TauCeti.Real.erfc_le_exp_neg_sq`, which come from Mills' ratio bound DLMF 7.8.2.

## References

* A. Cianchi, N. Fusco, F. Maggi and A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  Amer. J. Math. 133 (2011), 131–186, Lemma 3.4, inequality (3.2).
* M. Ledoux, *Concentration of measure and logarithmic Sobolev inequalities*, Séminaire de
  Probabilités XXXIII, Lecture Notes in Math. 1709, Springer, 1999, inequality (1.6), the bound
  `1 − Φ(r) ≤ e^{−r²/2}`.
* NIST Digital Library of Mathematical Functions, §7.8.
-/

public section

noncomputable section

open ProbabilityTheory

open scoped Real

namespace TauCeti.Probability

/-- The upper tail of the standard Gaussian law is half the complementary error function at
`r/√2`. -/
private theorem one_sub_cdf_gaussianReal_eq_erfc (r : ℝ) :
    1 - cdf (gaussianReal 0 1) r = TauCeti.Real.erfc (r / √2) / 2 := by
  rw [cdf_gaussianReal_zero_one, TauCeti.Real.erfc_def]
  ring

/-- **Mills' ratio bound** for the standard Gaussian law: for `r > 0`, the upper tail
`1 − Φ(r)` is strictly smaller than `φ(r)/r`. -/
theorem one_sub_cdf_gaussianReal_lt_gaussianPDFReal_div {r : ℝ} (hr : 0 < r) :
    1 - cdf (gaussianReal 0 1) r < gaussianPDFReal 0 1 r / r := by
  have h := TauCeti.Real.erfc_lt_exp_neg_sq_div (div_pos hr (by positivity : (0 : ℝ) < √2))
  rw [div_pow, Real.sq_sqrt zero_le_two] at h
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt zero_le_two
  simp only [one_sub_cdf_gaussianReal_eq_erfc, gaussianPDFReal_def, NNReal.coe_one, mul_one,
    sub_zero]
  rw [Real.sqrt_mul zero_le_two]
  calc TauCeti.Real.erfc (r / √2) / 2
      < Real.exp (-r ^ 2 / 2) / (√π * (r / √2)) / 2 := by gcongr; rwa [neg_div]
    _ = (√2 * √π)⁻¹ * Real.exp (-r ^ 2 / 2) / r := by
        field_simp
        linear_combination h2

/-- The standard Gaussian upper tail is at most half the Gaussian factor: for `r ≥ 0`,
`1 − Φ(r) ≤ e^{−r²/2}/2`, with equality at `r = 0`. -/
theorem one_sub_cdf_gaussianReal_le_exp_div_two {r : ℝ} (hr : 0 ≤ r) :
    1 - cdf (gaussianReal 0 1) r ≤ Real.exp (-r ^ 2 / 2) / 2 := by
  have h := TauCeti.Real.erfc_le_exp_neg_sq (div_nonneg hr (Real.sqrt_nonneg 2))
  rw [div_pow, Real.sq_sqrt zero_le_two, ← neg_div] at h
  rw [one_sub_cdf_gaussianReal_eq_erfc]
  gcongr

/-- For `r > 0` the bound `1 − Φ(r) ≤ e^{−r²/2}/2` is strict. -/
theorem one_sub_cdf_gaussianReal_lt_exp_div_two {r : ℝ} (hr : 0 < r) :
    1 - cdf (gaussianReal 0 1) r < Real.exp (-r ^ 2 / 2) / 2 := by
  have h := TauCeti.Real.erfc_lt_exp_neg_sq (div_pos hr (by positivity : (0 : ℝ) < √2))
  rw [div_pow, Real.sq_sqrt zero_le_two, ← neg_div] at h
  rw [one_sub_cdf_gaussianReal_eq_erfc]
  gcongr

end TauCeti.Probability
