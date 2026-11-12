/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import TauCeti.Analysis.SpecialFunctions.Hermite.FourierIntegral
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# A Gaussian moment bound for Hermite polynomials

The probabilists' Hermite polynomials, multiplied by the standard Gaussian, are uniformly
bounded by the corresponding absolute Gaussian moment. Dividing by the factorial gives a
bound with coefficient `2 ^ (-n / 2) / Gamma (n / 2 + 1)`, useful for absolute convergence
of series involving Hermite polynomials.
-/

public section

open scoped Real Nat NNReal
open MeasureTheory ProbabilityTheory

namespace TauCeti

private lemma fourier_moment_bound (n : ℕ) (y : ℝ) :
    Real.sqrt (2 * Real.pi) *
        (|Polynomial.aeval y (Polynomial.hermite n)| * Real.exp (-(y ^ 2) / 2)) ≤
      ∫ x : ℝ, |x| ^ n * Real.exp (-(x ^ 2) / 2) := by
  have heval : Polynomial.aeval (y : ℂ) (Polynomial.hermite n) =
      (Polynomial.aeval y (Polynomial.hermite n) : ℝ) :=
    Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) y _
  have hn := norm_integral_le_integral_norm (μ := volume)
    (fun s : ℝ => (s : ℂ) ^ n * Complex.exp (-(s : ℂ) ^ 2 / 2 - Complex.I * y * s))
  rw [integral_pow_mul_cexp_neg_sq_div_two_sub_I_mul] at hn
  simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), norm_neg, Complex.norm_I, one_pow,
    mul_one, heval, Complex.norm_exp] at hn
  have hre (s : ℝ) : (-(s : ℂ) ^ 2 / 2 - Complex.I * y * s).re = -(s ^ 2) / 2 := by
    simp [← Complex.ofReal_pow]
  have hre' : (-(y : ℂ) ^ 2 / 2).re = -(y ^ 2) / 2 := by
    simp [← Complex.ofReal_pow]
  simp only [hre, hre'] at hn
  simpa only [mul_assoc] using hn

/-- The Gaussian-weighted probabilists' Hermite polynomial is bounded by the absolute
Gaussian moment, expressed using the Gamma function after division by `n!`. -/
theorem abs_aeval_hermite_mul_exp_div_factorial_le (n : ℕ) (y : ℝ) :
    |Polynomial.aeval y (Polynomial.hermite n)| * Real.exp (-(y ^ 2) / 2) /
      (n.factorial : ℝ) ≤
      (2 : ℝ) ^ (-(n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
  -- Normalize the absolute moment already computed for the standard Gaussian law.
  have hmoment :
      ∫ x : ℝ, |x| ^ n * Real.exp (-(x ^ 2) / 2) =
        Real.sqrt (2 * Real.pi) *
          ((2 : ℝ) ^ ((n : ℝ) / 2) * Real.Gamma (((n : ℝ) + 1) / 2) / Real.sqrt Real.pi) := by
    have hm := TauCeti.Probability.integral_abs_sub_pow_gaussianReal 0 1 n
    simp only [sub_zero, NNReal.coe_one, mul_one] at hm
    rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)] at hm
    have hd : (fun x : ℝ => gaussianPDFReal 0 1 x • |x| ^ n) =
        fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ *
          (|x| ^ n * Real.exp (-(x ^ 2) / 2)) := by
      ext x
      simp [gaussianPDFReal]
      ring
    rw [hd, integral_const_mul] at hm
    calc
      _ = Real.sqrt (2 * Real.pi) *
          ((Real.sqrt (2 * Real.pi))⁻¹ *
            ∫ x : ℝ, |x| ^ n * Real.exp (-(x ^ 2) / 2)) := by
        rw [mul_inv_cancel_left₀ (by positivity : Real.sqrt (2 * Real.pi) ≠ 0)]
      _ = _ := by rw [hm]
  -- Legendre duplication converts the moment divided by `n!` to the desired coefficient.
  have hcoefficient :
      (2 : ℝ) ^ ((n : ℝ) / 2) * Real.Gamma (((n : ℝ) + 1) / 2) /
        Real.sqrt Real.pi / (n.factorial : ℝ) =
        (2 : ℝ) ^ (-(n : ℝ) / 2) / Real.Gamma ((n : ℝ) / 2 + 1) := by
    have hd := Real.Gamma_mul_Gamma_add_half (((n : ℝ) + 1) / 2)
    have harg : ((n : ℝ) + 1) / 2 + 1 / 2 = (n : ℝ) / 2 + 1 := by ring
    have harg' : 2 * (((n : ℝ) + 1) / 2) = (n : ℝ) + 1 := by ring
    have hexp : 1 - ((n : ℝ) + 1) = -(n : ℝ) := by ring
    rw [harg, harg', hexp, Real.Gamma_nat_eq_factorial] at hd
    have hp : (2 : ℝ) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-(n : ℝ)) =
        (2 : ℝ) ^ (-(n : ℝ) / 2) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hg : Real.Gamma ((n : ℝ) / 2 + 1) ≠ 0 :=
      (Real.Gamma_pos_of_pos (by positivity)).ne'
    have hs : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hf : (n.factorial : ℝ) ≠ 0 := by positivity
    apply (eq_div_iff hg).2
    calc
      _ = (2 : ℝ) ^ ((n : ℝ) / 2) *
          (Real.Gamma (((n : ℝ) + 1) / 2) * Real.Gamma ((n : ℝ) / 2 + 1)) /
          Real.sqrt Real.pi / (n.factorial : ℝ) := by ring
      _ = _ := by rw [hd]; field_simp; simpa only [neg_div] using hp
  rw [← hcoefficient]
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply le_of_mul_le_mul_left _ (by positivity : 0 < Real.sqrt (2 * Real.pi))
  rw [← hmoment]
  exact fourier_moment_bound n y

end TauCeti
