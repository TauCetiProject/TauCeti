/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.RingTheory.Polynomial.Hermite.Basic

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.RingTheory.Polynomial.Tower
import TauCeti.Analysis.SpecialFunctions.Erf.Series
import TauCeti.Analysis.SpecialFunctions.Hermite.FourierIntegral
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.RingTheory.Polynomial.Hermite.GeneratingFunction

/-!
# Gaussian moment and generating-series bounds for Hermite polynomials

The probabilists' Hermite polynomials, multiplied by the standard Gaussian, are uniformly
bounded by the corresponding absolute Gaussian moment. Dividing by the factorial gives a
bound with coefficient `2 ^ (-n / 2) / Gamma (n / 2 + 1)`, and multiplying by a complex power `w^m`
gives `‖He_m(y) w^m / m!‖ ≤ exp (y² / 2) * ((‖w‖ / √2)^m / Gamma (m / 2 + 1))`, useful for absolute
convergence of series involving Hermite polynomials.

Combining this termwise bound with the half-Gamma series majorant `< 2 exp(x²)` (DLMF 7.6.3)
and its arbitrary-shift vanishing-order bound yields polynomial-free and `O(‖w‖^M)` Gaussian
majorants for `M`-shifted tails of the Hermite exponential generating series (DLMF 18.12.15).

## Main results

* `TauCeti.abs_aeval_hermite_mul_exp_div_factorial_le`: Gaussian-weighted factorial bound
  `|He_n(y)| exp(-y² / 2) / n! ≤ 2 ^ (-n / 2) / Γ(n / 2 + 1)`.
* `TauCeti.norm_aeval_hermite_mul_pow_div_factorial_le`,
  `TauCeti.abs_aeval_hermite_mul_pow_div_factorial_le`: generating-series termwise bounds
  `‖He_m(y) w^m / m!‖ ≤ exp(y² / 2) (‖w‖ / √2)^m / Γ(m / 2 + 1)` (`y : ℝ`, `w : ℂ`) and
  `|He_m(y)| r^m / m! ≤ exp(y² / 2) (r / √2)^m / Γ(m / 2 + 1)` (`0 ≤ r`).
* `TauCeti.tsum_norm_aeval_hermite_mul_pow_div_factorial_add_lt`,
  `TauCeti.tsum_norm_aeval_hermite_mul_pow_div_factorial_add_le`: polynomial-free
  (`< 2 exp(y² / 2 + ‖w‖² / 2)`) and vanishing-order
  (`≤ 2 e exp(y² / 2) (‖w‖ / √2)^M exp(‖w‖² / 2)`) Gaussian majorants for `M`-shifted tails.

## References

* *NIST Digital Library of Mathematical Functions*, [§7.6](https://dlmf.nist.gov/7.6) and
  [§18.12](https://dlmf.nist.gov/18.12).
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
    Polynomial.aeval_algebraMap_apply ℂ y (Polynomial.hermite n)
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

/-- Uniform Gaussian-weighted bound on complex powers multiplied by real-argument Hermite
polynomials: for every `m : ℕ`, `y : ℝ`, and `w : ℂ`,
`‖He_m(y) w^m / m!‖ ≤ exp(y² / 2) * ((‖w‖ / √2)^m / Γ(m / 2 + 1))`. -/
theorem norm_aeval_hermite_mul_pow_div_factorial_le (m : ℕ) (y : ℝ) (w : ℂ) :
    ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * w ^ m / (m ! : ℂ)‖ ≤
      Real.exp (y ^ 2 / 2) * ((‖w‖ / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
  have heval : Polynomial.aeval (y : ℂ) (Polynomial.hermite m) =
      ((Polynomial.aeval y (Polynomial.hermite m) : ℝ) : ℂ) :=
    Polynomial.aeval_algebraMap_apply ℂ y (Polynomial.hermite m)
  have hnorm : ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite m) * w ^ m / (m ! : ℂ)‖ =
      |Polynomial.aeval y (Polynomial.hermite m)| * ‖w‖ ^ m / (m ! : ℝ) := by
    rw [heval, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
      Complex.norm_natCast]
  have hpow : (2 : ℝ) ^ (-(m : ℝ) / 2) * ‖w‖ ^ m = (‖w‖ / √2) ^ m := by
    rw [← Real.inv_sqrt_pow_eq_rpow (zero_le_two : (0 : ℝ) ≤ 2) m, ← mul_pow, inv_mul_eq_div]
  have hb := mul_le_mul_of_nonneg_left (abs_aeval_hermite_mul_exp_div_factorial_le m y)
    (by positivity : 0 ≤ Real.exp (y ^ 2 / 2) * ‖w‖ ^ m)
  have hexp : Real.exp (y ^ 2 / 2) * Real.exp (-(y ^ 2) / 2) = 1 := by
    rw [← Real.exp_add, neg_div, add_neg_cancel, Real.exp_zero]
  rw [hnorm]
  calc |Polynomial.aeval y (Polynomial.hermite m)| * ‖w‖ ^ m / (m ! : ℝ)
      = (Real.exp (y ^ 2 / 2) * Real.exp (-(y ^ 2) / 2)) *
          (|Polynomial.aeval y (Polynomial.hermite m)| * ‖w‖ ^ m / (m ! : ℝ)) := by
        rw [hexp, one_mul]
    _ = Real.exp (y ^ 2 / 2) * ‖w‖ ^ m *
          (|Polynomial.aeval y (Polynomial.hermite m)| * Real.exp (-(y ^ 2) / 2) /
            (m ! : ℝ)) := by ring
    _ ≤ Real.exp (y ^ 2 / 2) * ‖w‖ ^ m *
          ((2 : ℝ) ^ (-(m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2 + 1)) := hb
    _ = Real.exp (y ^ 2 / 2) *
          (((2 : ℝ) ^ (-(m : ℝ) / 2) * ‖w‖ ^ m) / Real.Gamma ((m : ℝ) / 2 + 1)) := by ring
    _ = Real.exp (y ^ 2 / 2) * ((‖w‖ / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by rw [hpow]

/-- Each term of the probabilists' Hermite exponential generating series at real `y` and
nonnegative real `r` satisfies `|He_m(y)| r^m / m! ≤ exp(y² / 2) (r / √2)^m / Γ(m / 2 + 1)`. -/
theorem abs_aeval_hermite_mul_pow_div_factorial_le (m : ℕ) (y : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    |Polynomial.aeval y (Polynomial.hermite m)| * r ^ m / m ! ≤
      Real.exp (y ^ 2 / 2) * ((r / √2) ^ m / Real.Gamma ((m : ℝ) / 2 + 1)) := by
  have h := norm_aeval_hermite_mul_pow_div_factorial_le m y (r : ℂ)
  rw [norm_div, norm_mul, norm_pow, ← Complex.coe_algebraMap, Polynomial.aeval_algebraMap_apply,
    Complex.coe_algebraMap, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_of_nonneg hr, Complex.norm_natCast] at h
  exact h

private theorem tsum_norm_aeval_hermite_mul_pow_div_factorial_add_le_mul_tsum
    (y : ℝ) (w : ℂ) (M : ℕ) :
    (∑' k : ℕ,
        ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
          ((k + M)! : ℂ)‖) ≤
      Real.exp (y ^ 2 / 2) *
        ∑' k : ℕ, (‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) := by
  rw [← tsum_mul_left]
  exact ((summable_nat_add_iff M).2
    (summable_norm_aeval_hermite_mul_pow_div_factorial (y : ℂ) w)).tsum_le_tsum
    (fun k => norm_aeval_hermite_mul_pow_div_factorial_le (k + M) y w)
    (((summable_nat_add_iff M).2
      (Real.summable_pow_div_Gamma_div_two_add_one (‖w‖ / √2))).mul_left (Real.exp (y ^ 2 / 2)))

/-- Polynomial-free Gaussian majorant for every `M`-shifted tail of the Hermite generating series:
`∑_{k ≥ 0} ‖He_{k + M}(y) w^{k + M} / (k + M)!‖ < 2 exp(y² / 2 + ‖w‖² / 2)`. -/
theorem tsum_norm_aeval_hermite_mul_pow_div_factorial_add_lt (y : ℝ) (w : ℂ) (M : ℕ) :
    (∑' k : ℕ,
        ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
          ((k + M)! : ℂ)‖) <
      2 * Real.exp (y ^ 2 / 2 + ‖w‖ ^ 2 / 2) := by
  have hlt := Real.tsum_pow_add_div_Gamma_div_two_add_one_lt_two_mul_exp (‖w‖ / √2) M
  have hsq : (‖w‖ / √2) ^ 2 = ‖w‖ ^ 2 / 2 := by rw [div_pow, Real.sq_sqrt zero_le_two]
  calc (∑' k : ℕ,
          ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
            ((k + M)! : ℂ)‖)
      ≤ Real.exp (y ^ 2 / 2) *
          ∑' k : ℕ, (‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) :=
          tsum_norm_aeval_hermite_mul_pow_div_factorial_add_le_mul_tsum y w M
    _ < Real.exp (y ^ 2 / 2) * (2 * Real.exp ((‖w‖ / √2) ^ 2)) :=
          mul_lt_mul_of_pos_left hlt (Real.exp_pos _)
    _ = 2 * Real.exp (y ^ 2 / 2 + ‖w‖ ^ 2 / 2) := by rw [hsq, Real.exp_add]; ring

/-- Vanishing-order Gaussian majorant for every `M`-shifted tail of the Hermite generating series:
`∑_{k ≥ 0} ‖He_{k + M}(y) w^{k + M} / (k + M)!‖ ≤ 2 e exp(y² / 2) (‖w‖ / √2)^M exp(‖w‖² / 2)`. -/
theorem tsum_norm_aeval_hermite_mul_pow_div_factorial_add_le (y : ℝ) (w : ℂ) (M : ℕ) :
    (∑' k : ℕ,
        ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
          ((k + M)! : ℂ)‖) ≤
      2 * Real.exp 1 * Real.exp (y ^ 2 / 2) * (‖w‖ / √2) ^ M * Real.exp (‖w‖ ^ 2 / 2) := by
  have htail := (le_abs_self _).trans
    (Real.abs_tsum_pow_add_div_Gamma_div_two_add_one_le_mul_exp (‖w‖ / √2) M)
  have hsq : (‖w‖ / √2) ^ 2 = ‖w‖ ^ 2 / 2 := by rw [div_pow, Real.sq_sqrt zero_le_two]
  rw [abs_of_nonneg (by positivity), hsq] at htail
  calc (∑' k : ℕ,
          ‖Polynomial.aeval (y : ℂ) (Polynomial.hermite (k + M)) * w ^ (k + M) /
            ((k + M)! : ℂ)‖)
      ≤ Real.exp (y ^ 2 / 2) *
          ∑' k : ℕ, (‖w‖ / √2) ^ (k + M) / Real.Gamma ((↑(k + M) : ℝ) / 2 + 1) :=
          tsum_norm_aeval_hermite_mul_pow_div_factorial_add_le_mul_tsum y w M
    _ ≤ Real.exp (y ^ 2 / 2) *
          (2 * Real.exp 1 * (‖w‖ / √2) ^ M * Real.exp (‖w‖ ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left htail (Real.exp_nonneg _)
    _ = 2 * Real.exp 1 * Real.exp (y ^ 2 / 2) * (‖w‖ / √2) ^ M * Real.exp (‖w‖ ^ 2 / 2) := by ring

end TauCeti
