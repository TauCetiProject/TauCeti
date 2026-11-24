/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.RingTheory.Binomial

/-!
# The expansion of the Gauss function at `1 / z` about a point `1 / z₀`

DLMF 15.15.1 expands the regularized Gauss function at a reciprocal argument in powers of
`(1 - z / z₀)⁻¹`, with terminating Gauss functions at `1 / z₀` as coefficients:

`𝐅(a, b; c; 1 / z) = (1 - z₀ / z)^{-a} ∑ₛ (a)ₛ / s! 𝐅(-s, b; c; 1 / z₀) (1 - z / z₀)^{-s}`,

for `z₀ ≠ 0` and `‖z - z₀‖ > max ‖z₀‖ ‖z₀ - 1‖`, with the principal power `(1 - z₀ / z)^{-a}`.
The coefficients `𝐅(-s, b; c; 1 / z₀)` are the polynomials `Complex.regularizedGaussHGFun (-s) b c`
evaluated at `z₀⁻¹`, which may lie anywhere in `ℂ`, including on the cut `[1, ∞)`.

This file proves the expansion for Euler's normalized integral `Complex.eulerIntegral a b c z⁻¹`,
which represents `𝐅(a, b; c; 1 / z)` when `0 < Re b < Re c` (DLMF 15.6.1). The hypothesis on `z`
puts `1 / z` off the cut `[1, ∞)`: a point `z ∈ (0, 1]` lies on the segment `[0, 1]`, where the
distance to `z₀` is at most `max ‖z₀‖ ‖z₀ - 1‖`.

For `t ∈ [0, 1]` the Euler kernel factors as

`1 - t / z = (1 - z₀ / z) (1 - (z₀ - t) / (z₀ - z))`,

where `‖(z₀ - t) / (z₀ - z)‖ ≤ max ‖z₀‖ ‖z₀ - 1‖ / ‖z - z₀‖ < 1`, and both factors lie in the open
right half-plane, so the principal power `(1 - t / z)^{-a}` splits. Expanding the second factor's
power in its binomial series and integrating term by term against the Beta weight gives the
expansion, since `(z₀ - t) / (z₀ - z) = (1 - z / z₀)⁻¹ (1 - t / z₀)` and Euler's integral with
first parameter `-s` is the terminating series
(`Complex.regularizedGaussHGFun_neg_natCast_eq_eulerIntegral`).

## Main results

* `Complex.hasSum_eulerIntegral_inv`: DLMF 15.15.1 for Euler's integral at `1 / z`.

## References

* NIST Digital Library of Mathematical Functions, equations 15.6.1 and 15.15.1,
  <https://dlmf.nist.gov/15.15>.
-/

public section

open MeasureTheory Set
open scoped Nat

namespace Complex

/-- On `[0, 1]`, the ratio `(z₀ - t) / (z₀ - z)` of the expansion is bounded by
`max ‖z₀‖ ‖z₀ - 1‖ / ‖z - z₀‖`: a point of `[0, 1]` is no farther from `z₀` than the farther
endpoint is. -/
private lemma norm_sub_ofReal_div_sub_le (z₀ z : ℂ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(z₀ - t) / (z₀ - z)‖ ≤ max ‖z₀‖ ‖z₀ - 1‖ / ‖z - z₀‖ := by
  have h : z₀ - t = ((1 - t : ℝ) : ℂ) * z₀ + (t : ℂ) * (z₀ - 1) := by push_cast; ring
  rw [norm_div, norm_sub_rev z₀ z, h]
  refine div_le_div_of_nonneg_right ((norm_add_le _ _).trans ?_) (norm_nonneg _)
  rw [norm_mul, norm_mul, Complex.norm_of_nonneg (sub_nonneg.mpr ht.2),
    Complex.norm_of_nonneg ht.1]
  nlinarith [le_max_left ‖z₀‖ ‖z₀ - 1‖, le_max_right ‖z₀‖ ‖z₀ - 1‖, ht.1, ht.2]

/-- The Euler kernel at `1 / z` splits as
`(1 - t / z)^{-a} = (1 - z₀ / z)^{-a} (1 - (z₀ - t) / (z₀ - z))^{-a}` on `[0, 1]`: both factors
lie in the open right half-plane, so their principal powers multiply. -/
private lemma one_sub_inv_mul_ofReal_cpow (a : ℂ) {z₀ z : ℂ}
    (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - z⁻¹ * t) ^ (-a) = (1 - z₀ / z) ^ (-a) * (1 - (z₀ - t) / (z₀ - z)) ^ (-a) := by
  have hzz₀ : 0 < ‖z - z₀‖ := (norm_nonneg _).trans_lt ((le_max_left _ _).trans_lt hz)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_sub, norm_neg] at hz
    exact (le_max_left _ _).not_gt hz
  have hz₀z : z₀ - z ≠ 0 := by rwa [← norm_pos_iff, norm_sub_rev]
  -- `1 - z₀ / z` is in the right half-plane, since `‖z₀ / z‖ < ‖1 - z₀ / z‖`.
  have hx : 0 < (1 - z₀ / z).re := by
    have h : ‖z₀ / z‖ < ‖1 - z₀ / z‖ := by
      rw [one_sub_div hz0, norm_div, norm_div]
      exact div_lt_div_of_pos_right ((le_max_left _ _).trans_lt hz) (norm_pos_iff.mpr hz0)
    have h2 := pow_lt_pow_left₀ h (norm_nonneg _) two_ne_zero
    rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, normSq_apply, normSq_apply] at h2
    simp only [sub_re, one_re, sub_im, one_im] at h2 ⊢
    nlinarith
  -- `1 - (z₀ - t) / (z₀ - z)` is in the right half-plane, since the ratio has norm below `1`.
  have hy : 0 < (1 - (z₀ - t) / (z₀ - z)).re := by
    rw [sub_re, one_re, sub_pos]
    exact (re_le_norm _).trans_lt ((norm_sub_ofReal_div_sub_le z₀ z ht).trans_lt
      ((div_lt_one hzz₀).mpr hz))
  rw [← TauCeti.mul_cpow_of_re_pos hx hy]
  congr 1
  field_simp
  ring

/-- The `n`-th term of the expansion integrated against the Beta weight: since
`(z₀ - t) / (z₀ - z) = (1 - z / z₀)⁻¹ (1 - t / z₀)`, it is a terminating Euler integral at
`1 / z₀`. -/
private lemma inv_Gamma_mul_integral_multichoose_mul_pow (a : ℂ) {b c z₀ z : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) (hz₀ : z₀ ≠ 0) (hz : z₀ - z ≠ 0) (n : ℕ) :
    (Gamma b * Gamma (c - b))⁻¹ * ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) *
        (1 - (t : ℂ)) ^ (c - b - 1) * (Ring.multichoose a n * ((z₀ - t) / (z₀ - z)) ^ n) =
      (ascPochhammer ℂ n).eval a / n ! * regularizedGaussHGFun (-n) b c z₀⁻¹ *
        ((1 - z / z₀) ^ n)⁻¹ := by
  rw [regularizedGaussHGFun_neg_natCast_eq_eulerIntegral n hb hbc, eulerIntegral_def,
    TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer]
  have hint : (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        ((n ! : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a * ((z₀ - t) / (z₀ - z)) ^ n)) =
      (n ! : ℂ)⁻¹ * (ascPochhammer ℂ n).eval a * ((1 - z / z₀) ^ n)⁻¹ *
        ∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - z₀⁻¹ * t) ^ (-(-(n : ℂ))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [neg_neg, cpow_natCast, show (z₀ - t) / (z₀ - z) = (1 - z / z₀)⁻¹ *
      (1 - z₀⁻¹ * t) by field_simp, mul_pow, inv_pow]
    ring
  rw [hint]
  ring

/-- **DLMF 15.15.1** for Euler's integral: when `0 < Re b < Re c`, `z₀ ≠ 0` and
`‖z - z₀‖ > max ‖z₀‖ ‖z₀ - 1‖`,

`E(a, b, c, 1 / z) = (1 - z₀ / z)^{-a} ∑ₛ (a)ₛ / s! 𝐅(-s, b; c; 1 / z₀) (1 - z / z₀)^{-s}`,

with the series convergent and the coefficients the polynomials `regularizedGaussHGFun (-s) b c`
at `z₀⁻¹`. -/
theorem hasSum_eulerIntegral_inv (a : ℂ) {b c z₀ z : ℂ} (hb : 0 < b.re) (hbc : b.re < c.re)
    (hz₀ : z₀ ≠ 0) (hz : max ‖z₀‖ ‖z₀ - 1‖ < ‖z - z₀‖) :
    HasSum (fun s : ℕ => (1 - z₀ / z) ^ (-a) *
        ((ascPochhammer ℂ s).eval a / s ! * regularizedGaussHGFun (-s) b c z₀⁻¹ *
          ((1 - z / z₀) ^ s)⁻¹))
      (eulerIntegral a b c z⁻¹) := by
  have hzz₀ : 0 < ‖z - z₀‖ := (norm_nonneg _).trans_lt ((le_max_left _ _).trans_lt hz)
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)
  let v : ℝ → ℂ := fun t => (z₀ - t) / (z₀ - z)
  -- Expand `(1 - v t) ^ (-a)` in its binomial series and integrate term by term; the ratio
  -- `v t` is bounded on `[0, 1]` by `max ‖z₀‖ ‖z₀ - 1‖ / ‖z - z₀‖ < 1`.
  have hdct := TauCeti.hasSum_integral_mul_multichoose_mul_pow a (w := w) (v := v)
    (betaIntegral_convergent hb (by simpa using sub_pos.mpr hbc)) (by fun_prop)
    ((div_lt_one hzz₀).mpr hz) fun t ht => norm_sub_ofReal_div_sub_le z₀ z (Ioc_subset_Icc_self ht)
  convert hdct.mul_left ((1 - z₀ / z) ^ (-a) * (Gamma b * Gamma (c - b))⁻¹) using 1
  · ext n
    have hz₀z : z₀ - z ≠ 0 := by rwa [← norm_pos_iff, norm_sub_rev]
    simp only [w, v]
    rw [mul_assoc ((1 - z₀ / z) ^ (-a)) (Gamma b * Gamma (c - b))⁻¹,
      inv_Gamma_mul_integral_multichoose_mul_pow a hb hbc hz₀ hz₀z n]
  · -- The value is Euler's integral at `z⁻¹`, after splitting the kernel.
    rw [eulerIntegral_def, mul_comm _ (Gamma b * Gamma (c - b))⁻¹, mul_assoc]
    congr 1
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    simp only [w, v, one_sub_inv_mul_ofReal_cpow a hz ht]
    ring

end Complex
