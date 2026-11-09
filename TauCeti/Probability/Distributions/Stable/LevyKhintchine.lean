/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Stable.CompensatedIntegral
public import TauCeti.Probability.Distributions.Stable.Exponent
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Integral.RpowLaplace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The Lévy–Khintchine formula for stable exponents

For `0 < α < 2` and `|β| ≤ 1`, let `ν` be the stable Lévy measure `stableLevyMeasure α β`, with
density `Γ(1 + α) sin(πα/2) / π * ((1 + β) 1_{x > 0} + (1 - β) 1_{x < 0}) |x| ^ (-1 - α)`.
This file proves that for every real `t`,

`∫ x, exp (i t x) - 1 - i t sin x ∂ν = stableCharacteristicExponent α β t`,

so the sine-compensated Lévy integral is exactly the stable characteristic exponent `Ψ_{α,β}`
in Nolan's `S₀` parameterization, including the logarithmic branch at `α = 1` and both
full-skewness boundaries. Combined with the compensated compound-Poisson approximations, this
identifies the limit of their characteristic functions as `exp (Ψ_{α,β} t)`.

## Proof

Reflection reduces the integral to the positive half-line
(`TauCeti.Probability.integral_stableLevyMeasure_eq`), where the weight `x ^ (-(α + 1))`
is written as a Gamma mixture of exponentials (`TauCeti.integral_Ioi_rpow_neg_smul`). The
Laplace transform of the compensated kernel is the rational function
`(s - i t)⁻¹ - s⁻¹ - i t / (1 + s ^ 2)`
(`TauCeti.integral_Ioi_exp_neg_mul_smul_cexp_sub_one_sub_sin`), and the remaining
power-weighted integrals reduce to `∫ y in Ioi 0, y ^ (s - 1) / (y ^ 2 + t ^ 2)`, evaluated by
Euler's reflection formula (`TauCeti.integral_rpow_div_sq_add_sq`). The imaginary part needs
three cases: below and above shape one the integrand splits into two such integrals, and at
shape one it has an elementary logarithmic primitive
(`TauCeti.integral_mul_div_sq_add_sq_sub_div_one_add_sq`).

## References

* J. P. Nolan, *Univariate Stable Distributions: Models for Heavy Tailed Data*, Springer,
  2020, chapter 1.
* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, section 14.
-/

public section

noncomputable section

open MeasureTheory Real Set Filter
open scoped Topology

namespace TauCeti.Probability

/-- The power-weighted Laplace transform of the compensated kernel is a multiple of the
totally skewed stable exponent. -/
private lemma integral_rpow_smul_laplace {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (t : ℝ)
    (hint : IntegrableOn (fun s : ℝ ↦ s ^ α • (((s / (s ^ 2 + t ^ 2) - s⁻¹ : ℝ) : ℂ) +
      ((t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I)) (Ioi 0)) :
    ∫ s in Ioi (0 : ℝ), s ^ α • (((s / (s ^ 2 + t ^ 2) - s⁻¹ : ℝ) : ℂ) +
      ((t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I) =
      (π / (2 * sin (π * α / 2))) • stableCharacteristicExponent α 1 t := by
  have hsin : sin (π * α / 2) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [pi_pos])).ne'
  apply Complex.ext
  · rw [← RCLike.re_to_complex, ← integral_re hint]
    simp only [RCLike.re_to_complex, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.mul_im, mul_zero, sub_zero, zero_mul, add_zero, mul_one,
      stableCharacteristicExponent_re hα.ne']
    rw [integral_rpow_mul_div_sq_add_sq_sub_inv hα hα2 t]
    ring
  · rw [← RCLike.im_to_complex, ← integral_im hint]
    simp only [RCLike.im_to_complex, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
      Complex.mul_im, mul_zero, sub_zero, zero_mul, add_zero, mul_one, zero_add]
    rcases lt_trichotomy α 1 with h1 | rfl | h1
    · rw [integral_rpow_mul_div_sq_add_sq_sub_div_one_add_sq (by linarith)
        (by linarith) h1.ne t,
        stableCharacteristicExponent_im_of_ne_one h1.ne, one_mul, tan_eq_sin_div_cos]
      have hcos : cos (π * α / 2) ≠ 0 :=
        (cos_pos_of_mem_Ioo ⟨by nlinarith [pi_pos], by nlinarith [pi_pos]⟩).ne'
      rw [mul_comm π α] at hsin hcos ⊢
      field_simp
    · simp only [rpow_one]
      rw [integral_mul_div_sq_add_sq_sub_div_one_add_sq t, stableCharacteristicExponent_one,
        mul_one, sin_pi_div_two]
      simp only [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re]
      field_simp
      ring
    · rw [integral_rpow_mul_div_sq_add_sq_sub_div_one_add_sq (by linarith)
        (by linarith) h1.ne' t,
        stableCharacteristicExponent_im_of_ne_one h1.ne', one_mul, tan_eq_sin_div_cos]
      have hcos : cos (π * α / 2) ≠ 0 :=
        (cos_neg_of_pi_div_two_lt_of_lt (by nlinarith [pi_pos]) (by nlinarith [pi_pos])).ne
      rw [mul_comm π α] at hsin hcos ⊢
      field_simp

variable {α β : ℝ}

/-- **The Lévy–Khintchine formula for stable exponents.** For `0 < α < 2` and `|β| ≤ 1`,
integrating the sine-compensated characteristic kernel against the stable Lévy measure gives
the stable characteristic exponent in Nolan's `S₀` parameterization. -/
theorem integral_exp_sub_one_sub_sin_stableLevyMeasure (hα : α ∈ Ioo 0 2) (hβ : |β| ≤ 1)
    (t : ℝ) :
    ∫ x, Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I
      ∂stableLevyMeasure α β = stableCharacteristicExponent α β t := by
  have hhalf (t : ℝ) : ∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) •
      (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I) =
      ((Gamma (α + 1))⁻¹ * (π / (2 * sin (π * α / 2)))) •
        stableCharacteristicExponent α 1 t := by
    have h0 := (integrable_stableLevyDensity_smul_iff α 0).mp
      (integrable_exp_sub_one_sub_sin_stableLevyMeasure α 0 t)
    have hc := stableLevyDensity_coefficient_pos hα
    have h0' : IntegrableOn (fun x : ℝ ↦ x ^ (-(α + 1)) •
        (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I)) (Ioi 0) := by
      refine IntegrableOn.congr_fun
        (Integrable.smul (Gamma (1 + α) * sin (π * α / 2) / π)⁻¹ h0.integrableOn)
        (fun x (hx : 0 < x) ↦ ?_) measurableSet_Ioi
      have hβ0 : |(0 : ℝ)| ≤ 1 := by simp
      rw [Pi.smul_apply, stableLevyDensity_of_ne_zero hα hβ0 hx.ne', ite_eq_left hx,
        abs_of_pos hx, add_zero, mul_one, smul_smul, inv_mul_cancel_left₀ hc.ne']
    have hα1 : -1 < α := by linarith [hα.1]
    have hint := integrableOn_rpow_smul_integral_exp_neg_mul_smul hα1 h0'
    have hL : EqOn (fun s : ℝ ↦ s ^ α • ∫ x in Ioi (0 : ℝ), exp (-(x * s)) •
        (Complex.exp ((t * x : ℝ) * Complex.I) - 1 - (t * sin x : ℝ) * Complex.I))
        (fun s : ℝ ↦ s ^ α • (((s / (s ^ 2 + t ^ 2) - s⁻¹ : ℝ) : ℂ) +
          ((t / (s ^ 2 + t ^ 2) - t / (1 + s ^ 2) : ℝ) : ℂ) * Complex.I)) (Ioi 0) :=
      fun s (hs : 0 < s) ↦ by simp only [integral_Ioi_exp_neg_mul_smul_cexp_sub_one_sub_sin hs t]
    rw [integral_Ioi_rpow_neg_smul hα1 h0', setIntegral_congr_fun measurableSet_Ioi hL,
      integral_rpow_smul_laplace hα.1 hα.2 t (hint.congr_fun hL measurableSet_Ioi), smul_smul]
  have hneg : ∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) •
      (Complex.exp ((t * -x : ℝ) * Complex.I) - 1 - (t * sin (-x) : ℝ) * Complex.I) =
      ∫ x in Ioi (0 : ℝ), x ^ (-(α + 1)) •
        (Complex.exp ((-t * x : ℝ) * Complex.I) - 1 - (-t * sin x : ℝ) * Complex.I) := by
    simp only [mul_neg, sin_neg, neg_mul]
  rw [integral_stableLevyMeasure_eq hα hβ (integrable_exp_sub_one_sub_sin_stableLevyMeasure α β t)]
  rw [hneg, hhalf, hhalf, smul_smul, smul_smul, add_comm 1 α]
  have hsin : sin (π * α / 2) ≠ 0 :=
    (sin_pos_of_pos_of_lt_pi (by nlinarith [pi_pos, hα.1]) (by nlinarith [pi_pos, hα.2])).ne'
  have hΓ : Gamma (α + 1) ≠ 0 := (Gamma_pos_of_pos (by linarith [hα.1])).ne'
  have hcoef (b : ℝ) : Gamma (α + 1) * sin (π * α / 2) / π * b *
      ((Gamma (α + 1))⁻¹ * (π / (2 * sin (π * α / 2)))) = b / 2 := by
    rw [mul_comm π α] at hsin ⊢
    field_simp
  rw [hcoef, hcoef, stableCharacteristicExponent_neg]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.conj_re,
      stableCharacteristicExponent_re hα.1.ne']
    ring
  · simp only [Complex.add_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, Complex.conj_im,
      stableCharacteristicExponent_im_eq_mul α β t]
    ring

end TauCeti.Probability
