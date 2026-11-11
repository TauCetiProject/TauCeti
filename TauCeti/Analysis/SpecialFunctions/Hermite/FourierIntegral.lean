/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

/-!
# Gaussian Fourier moments and Hermite polynomials

The Fourier transform of a monomial times the Gaussian `exp (-s²/2)` is the
probabilists' Hermite polynomial times the Gaussian `exp (-y²/2)`, with factor
`√(2π) (-i)ⁿ`. The formula uses angular frequency, so its kernel is `exp (-iys)`.
It supplies an integral representation suitable for uniform bounds on the
Gaussian-weighted Hermite polynomials.

The proof combines Mathlib's `Real.iteratedDeriv_fourier` and Gaussian Fourier
transform with `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`.

## References

* NIST DLMF, [18.10.10](https://dlmf.nist.gov/18.10#E10), after rescaling from
  the physicists' to the probabilists' Hermite polynomials and reversing the
  Fourier-frequency sign.
-/

public section

namespace TauCeti

open MeasureTheory Polynomial Real Complex
open scoped FourierTransform

private theorem gaussian_fourier_half :
    𝓕 (fun x : ℝ => (Real.exp (-(x ^ 2 / 2)) : ℂ)) =
      fun w : ℝ => (Real.sqrt (2 * π) : ℂ) *
        (Real.exp (-((2 * π * w) ^ 2 / 2)) : ℂ) := by
  funext w
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [smul_eq_mul]
  have h := fourierIntegral_gaussian (b := (1 / 2 : ℂ)) (by norm_num) (-(2 * π * w))
  have hconst : (π / (1 / 2 : ℂ)) ^ (1 / 2 : ℂ) = (Real.sqrt (2 * π) : ℂ) := by
    rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by positivity)]
    push_cast
    congr 1
    ring_nf
  rw [hconst] at h
  convert h using 1
  · congr 1
    funext x
    rw [Complex.ofReal_exp]
    congr 1
    · push_cast
      ring_nf
    · push_cast
      ring_nf
  · congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf

private theorem iteratedDeriv_gaussian_half_complex (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ => (Real.exp (-(y ^ 2 / 2)) : ℂ)) x =
      ((-1 : ℝ) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2)) : ℝ) := by
  have h := iteratedDeriv_smul_const (𝕜 := ℝ) (𝔸 := ℝ)
    (f := fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (v := (1 : ℂ))
    (n := n) (x := x) (by fun_prop)
  simpa only [Complex.real_smul, mul_one, iteratedDeriv_eq_iterate,
    deriv_gaussian_eq_hermite_mul_gaussian] using h

/-- Polynomial moments of the angular-frequency Gaussian Fourier kernel are integrable. -/
theorem integrable_pow_mul_cexp_gaussian (n : ℕ) (y : ℝ) :
    Integrable (fun s : ℝ => (s : ℂ) ^ n *
      Complex.exp (-(s : ℂ) ^ 2 / 2 - Complex.I * y * s)) := by
  have hint := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    (s := (n : ℝ)) (lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n))
  simp only [Real.rpow_natCast] at hint
  apply (integrable_norm_iff (by fun_prop)).mp
  convert hint.norm using 1
  funext s
  simp only [norm_mul, norm_pow, Complex.norm_real, Complex.norm_exp,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  congr 1
  congr 1
  simp [Complex.mul_re, Complex.mul_im, pow_two]
  ring

private theorem fourier_pow_mul_gaussian_half (n : ℕ) (y : ℝ) :
    𝓕 (fun x : ℝ => (-2 * π * I * x) ^ n •
      (Real.exp (-(x ^ 2 / 2)) : ℂ)) (y / (2 * π)) =
    (-2 * π * I : ℂ) ^ n *
      ∫ s : ℝ, (s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 / 2 - I * y * s) := by
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  congr 1
  funext s
  simp only [smul_eq_mul, mul_pow, Complex.ofReal_exp]
  rw [sub_eq_add_neg, Complex.exp_add]
  have hphase : ((-2 * π * s * (y / (2 * π)) : ℝ) : ℂ) * I =
      -(I * y * s) := by
    push_cast
    field_simp
  rw [hphase]
  have hgauss : ((-(s ^ 2 / 2) : ℝ) : ℂ) = -(s : ℂ) ^ 2 / 2 := by push_cast; ring
  rw [hgauss]
  ring

/-- Fourier representation of the probabilists' Hermite polynomial times its Gaussian weight. -/
theorem integral_pow_mul_cexp_gaussian (n : ℕ) (y : ℝ) :
    (∫ s : ℝ, (s : ℂ) ^ n *
      Complex.exp (-(s : ℂ) ^ 2 / 2 - Complex.I * y * s)) =
    (Real.sqrt (2 * Real.pi) : ℂ) * (-Complex.I) ^ n *
      Polynomial.aeval (y : ℂ) (Polynomial.hermite n) *
      Complex.exp (-(y : ℂ) ^ 2 / 2) := by
  let g : ℝ → ℂ := fun x => (Real.exp (-(x ^ 2 / 2)) : ℂ)
  have hint (k : ℕ) : Integrable (fun x : ℝ => x ^ k • g x) := by
    refine (integrable_pow_mul_cexp_gaussian k 0).congr
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [g, Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_zero,
      mul_zero, zero_mul, sub_zero]
    congr 2 <;> push_cast <;> ring
  -- Differentiate the Gaussian transform and evaluate at the angular frequency.
  have hfourier := congrFun (Real.iteratedDeriv_fourier (N := ⊤)
    (f := g) (fun k _ => hint k) (n := n) (by simp)) (y / (2 * π))
  have hderiv : iteratedDeriv n (𝓕 g) (y / (2 * π)) =
      (Real.sqrt (2 * π) : ℂ) * (2 * π : ℂ) ^ n *
        ((-1 : ℝ) ^ n * aeval y (hermite n) * Real.exp (-(y ^ 2 / 2)) : ℝ) := by
    have hreal : ContDiff ℝ n (fun x : ℝ => Real.exp (-(x ^ 2 / 2))) := by fun_prop
    have hg : ContDiff ℝ n g := Complex.ofRealCLM.contDiff.comp hreal
    rw [gaussian_fourier_half, iteratedDeriv_const_mul_field,
      iteratedDeriv_comp_const_smul hg]
    simp only [Complex.real_smul, Complex.ofReal_pow]
    have hy : 2 * π * (y / (2 * π)) = y := by field_simp
    rw [hy, iteratedDeriv_gaussian_half_complex]
    push_cast
    ring
  rw [hderiv] at hfourier
  rw [fourier_pow_mul_gaussian_half] at hfourier
  -- Cancel the Fourier differentiation factor and simplify its phase.
  have hc : (-2 * π * I : ℂ) ^ n ≠ 0 := by
    apply pow_ne_zero
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr pi_ne_zero)) I_ne_zero
  apply mul_left_cancel₀ hc
  rw [← hfourier]
  have hpow : (-2 * π * I : ℂ) ^ n * (-I) ^ n =
      (2 * π : ℂ) ^ n * (-1) ^ n := by
    rw [← mul_pow, ← mul_pow]
    congr 1
    ring_nf
    simp [I_sq]
  have heval : (aeval y (hermite n) : ℂ) = aeval (y : ℂ) (hermite n) := by
    exact (Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y (hermite n)).symm
  rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one, heval, Complex.ofReal_exp]
  have he : ((-(y ^ 2 / 2) : ℝ) : ℂ) = -(y : ℂ) ^ 2 / 2 := by push_cast; ring
  rw [he]
  linear_combination -(Real.sqrt (2 * π) : ℂ) * aeval (y : ℂ) (hermite n) *
    Complex.exp (-(y : ℂ) ^ 2 / 2) * hpow

end TauCeti
