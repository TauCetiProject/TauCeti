/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.RingTheory.Polynomial.Hermite.Derivative

/-!
# Gaussian Fourier moments and Hermite polynomials

The Fourier transform of a monomial times the Gaussian `exp (-s²/2)` is the
probabilists' Hermite polynomial times the Gaussian `exp (-y²/2)`, with factor
`√(2π) (-i)ⁿ`. The formula uses angular frequency, so its kernel is `exp (-iys)`,
and holds for every complex frequency `y`. Its restriction to real frequencies supplies
an integral representation suitable for uniform bounds on the Gaussian-weighted
Hermite polynomials.

The proof starts with Mathlib's `fourierIntegral_gaussian` and uses integration
by parts together with the three-term Hermite recurrence.

## References

* NIST DLMF, [18.10.10](https://dlmf.nist.gov/18.10#E10), after rescaling from
  the physicists' to the probabilists' Hermite polynomials and reversing the
  Fourier-frequency sign.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real Complex

/-- Polynomial moments of the angular-frequency Gaussian Fourier kernel are integrable
at every complex frequency. -/
theorem integrable_pow_mul_cexp_neg_sq_div_two_sub_I_mul (n : ℕ) (y : ℂ) :
    Integrable (fun s : ℝ => (s : ℂ) ^ n *
      Complex.exp (-(s : ℂ) ^ 2 / 2 - Complex.I * y * s)) := by
  have hint := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 4) (by norm_num)
    (s := (n : ℝ)) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
  simp only [Real.rpow_natCast] at hint
  apply (hint.norm.const_mul (Real.exp (y.im ^ 2))).mono' (by fun_prop)
  filter_upwards [] with s
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
    abs_exp]
  have hre : (-(s : ℂ) ^ 2 / 2 - I * y * s).re = -s ^ 2 / 2 + y.im * s := by
    simp [Complex.mul_re, Complex.mul_im, pow_two]
  rw [hre]
  calc
    |s| ^ n * Real.exp (-s ^ 2 / 2 + y.im * s) ≤
        |s| ^ n * Real.exp (y.im ^ 2 - 1 / 4 * s ^ 2) := by
      gcongr
      nlinarith [sq_nonneg (s / 2 - y.im)]
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add, neg_mul]
      ring

private theorem integral_pow_mul_cexp_recurrence (n : ℕ) (y : ℂ) :
    (∫ s : ℝ, (s : ℂ) ^ (n + 1) * Complex.exp (-(s : ℂ) ^ 2 / 2 - I * y * s)) =
      -I * y * (∫ s : ℝ, (s : ℂ) ^ n *
        Complex.exp (-(s : ℂ) ^ 2 / 2 - I * y * s)) +
      n * (∫ s : ℝ, (s : ℂ) ^ (n - 1) *
        Complex.exp (-(s : ℂ) ^ 2 / 2 - I * y * s)) := by
  let g : ℝ → ℂ := fun s => Complex.exp (-(s : ℂ) ^ 2 / 2 - I * y * s)
  have hint (k : ℕ) : Integrable (fun s : ℝ => (s : ℂ) ^ k * g s) :=
    integrable_pow_mul_cexp_neg_sq_div_two_sub_I_mul k y
  have hpow (s : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) ^ n)
      ((n : ℂ) * (s : ℂ) ^ (n - 1)) s := by
    simpa using! (Complex.ofRealCLM.hasDerivAt (x := s)).fun_pow n
  have hg (s : ℝ) : HasDerivAt g ((-(s : ℂ) - I * y) * g s) s := by
    have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := by
      simpa using! Complex.ofRealCLM.hasDerivAt (x := s)
    convert (((hid.fun_pow 2).fun_neg.div_const 2).fun_sub
      (hid.const_mul (I * y))).cexp using 1
    simp only [g, Nat.cast_ofNat, mul_one]
    ring
  have huv' : Integrable (fun s : ℝ => (s : ℂ) ^ n * (-(s : ℂ) - I * y) * g s) := by
    convert ((hint (n + 1)).neg.sub ((hint n).const_mul (I * y))) using 1
    funext s
    simp only [Pi.sub_apply, Pi.neg_apply, pow_succ]
    ring
  have hu'v : Integrable (fun s : ℝ => (n : ℂ) * (s : ℂ) ^ (n - 1) * g s) := by
    simpa only [mul_assoc] using (hint (n - 1)).const_mul (n : ℂ)
  -- Integrate by parts; integrability supplies the vanishing boundary terms.
  have h := integral_bilinear_hasDerivAt_right_eq_neg_left_of_integrable
    (L := ContinuousLinearMap.mul ℝ ℂ)
    (fun s _ => hpow s) (fun s _ => hg s)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_assoc] using! huv')
    (by simpa only [ContinuousLinearMap.mul_apply'] using! hu'v)
    (by simpa only [ContinuousLinearMap.mul_apply'] using! hint n)
  simp only [ContinuousLinearMap.mul_apply'] at h
  have heq : (fun s : ℝ => (s : ℂ) ^ n * ((-(s : ℂ) - I * y) * g s)) =
      fun s : ℝ => -((s : ℂ) ^ (n + 1) * g s) - I * y * ((s : ℂ) ^ n * g s) := by
    funext s
    rw [pow_succ]
    ring
  have hneg : Integrable (fun s : ℝ => -((s : ℂ) ^ (n + 1) * g s)) := by
    simpa only [Pi.neg_apply] using! (hint (n + 1)).neg
  rw [heq, integral_sub hneg ((hint n).const_mul _), integral_neg,
    integral_const_mul] at h
  simp only [mul_assoc] at h
  rw [integral_const_mul] at h
  dsimp only [g] at h
  linear_combination -h

/-- Fourier representation of the probabilists' Hermite polynomial times its Gaussian weight,
valid at every complex frequency. -/
theorem integral_pow_mul_cexp_neg_sq_div_two_sub_I_mul (n : ℕ) (y : ℂ) :
    (∫ s : ℝ, (s : ℂ) ^ n *
      Complex.exp (-(s : ℂ) ^ 2 / 2 - Complex.I * y * s)) =
    (Real.sqrt (2 * Real.pi) : ℂ) * (-Complex.I) ^ n *
      Polynomial.aeval y (Polynomial.hermite n) * Complex.exp (-y ^ 2 / 2) := by
  have hzero : (∫ s : ℝ, (s : ℂ) ^ 0 *
      Complex.exp (-(s : ℂ) ^ 2 / 2 - I * y * s)) =
      (Real.sqrt (2 * π) : ℂ) * Complex.exp (-y ^ 2 / 2) := by
    have h := fourierIntegral_gaussian (b := (1 / 2 : ℂ)) (by norm_num) (-y)
    have hconst : (π / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (2 * π) : ℂ) := by
      rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
      push_cast
      congr 1
      ring_nf
    rw [hconst] at h
    convert h using 1
    · congr 1
      funext s
      rw [pow_zero, one_mul, ← Complex.exp_add]
      congr 1
      ring
    · congr 1
      congr 1
      ring
  induction n using Nat.twoStepInduction with
  | zero => simpa using hzero
  | one =>
      rw [integral_pow_mul_cexp_recurrence, hzero]
      simp only [Nat.cast_zero, zero_mul, add_zero, pow_one, hermite_one, aeval_X]
      ring
  | more n hn hn' =>
      rw [integral_pow_mul_cexp_recurrence,
        Nat.add_sub_cancel, hn, hn', hermite_add_two, map_sub, map_mul, aeval_X,
        map_nsmul, nsmul_eq_mul, pow_succ, pow_succ, Nat.cast_add, Nat.cast_one]
      ring_nf
      simp [I_sq]

end TauCeti
