/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf.Basic

import TauCeti.Analysis.Complex.IteratedDeriv
import TauCeti.Analysis.SpecialFunctions.Gaussian.Deriv
import TauCeti.Analysis.SpecialFunctions.Gaussian.LaplaceIntegral
import TauCeti.Analysis.SpecialFunctions.Gaussian.Moments
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Repeated integrals of the Gaussian

This file defines the repeated Gaussian integrals

$$
\mathrm{Hh}_n(z) = \int_0^\infty \frac{t^n}{n!}\, e^{-(z+t)^2/2}\, dt, \qquad n \in \mathbb{N},
$$

for complex `z`, and develops their basic theory. The integral runs along the horizontal ray
`z + t`, `t ≥ 0`, from `z` towards `+∞`. Writing `Hh_{-1}(z)` for `e^{-z²/2}`, the integral `Hh_n`
is the `(n + 1)`-fold repeated integral of `Hh_{-1}` along this ray:
`Hh_{n+1}(z) = ∫₀^∞ Hh_n(z + t) dt`. The integrals converge absolutely for every `n` and `z`,
and each `Hh_n` is entire with `Hh₀′(z) = -e^{-z²/2}` and `Hh_{n+1}′(z) = -Hh_n(z)`. They satisfy
`Hh₁(z) = e^{-z²/2} - z Hh₀(z)` and the three-term recurrence
`(n + 2) Hh_{n+2}(z) = Hh_n(z) - z Hh_{n+1}(z)`. At the origin
`Hh_n(0) = 2^{(n-1)/2} Γ((n + 1)/2) / n!`, and `Hh_n(x)` is real and positive for real `x`,
with `Hh₀(x) = √(π/2) erfc(x/√2)`. The `k`-th derivative of `Hh_{n+k}` is `(-1)ᵏ Hh_n`, and the
`k`-th derivative of the weighted function `e^{z²/2} Hh_n(z)` is
`(-1)ᵏ (n + k)!/n! e^{z²/2} Hh_{n+k}(z)`.

These functions enter the theory of parabolic cylinder functions through DLMF 12.7.7, which
expresses the half-integer values of `U` as `U(n + ½, z) = e^{z²/4} Hh_n(z)`. That identity is
not proved here: this file develops `Hh_n` itself, from the defining integral alone.

## Main declarations

* `TauCeti.repeatedGaussianIntegral`: the repeated Gaussian integral `Hh_n(z)`.
* `TauCeti.integrableOn_repeatedGaussianIntegral_integrand`: the defining integral converges
  absolutely.
* `TauCeti.repeatedGaussianIntegral_eq_cexp_div_factorial_mul_integral`: the Laplace form
  `Hh_n(z) = e^{-z²/2}/n! ∫₀^∞ tⁿ e^{-t²/2 - zt} dt`.
* `TauCeti.hasDerivAt_repeatedGaussianIntegral_zero`,
  `TauCeti.hasDerivAt_repeatedGaussianIntegral_succ`,
  `TauCeti.differentiable_repeatedGaussianIntegral`: the derivatives, and entirety.
* `TauCeti.repeatedGaussianIntegral_one`, `TauCeti.repeatedGaussianIntegral_add_two`: the
  recurrences.
* `TauCeti.norm_repeatedGaussianIntegral_le`: Gaussian decay `‖Hh_n(z)‖ ≤ e^{(y² - x²)/2} Hh_n(0)`
  for `z = x + iy` with `x ≥ 0`.
* `TauCeti.integrableOn_repeatedGaussianIntegral_add`,
  `TauCeti.repeatedGaussianIntegral_succ_eq_integral`: the repeated-integral characterization
  `Hh_{n+1}(z) = ∫₀^∞ Hh_n(z + t) dt`.
* `TauCeti.repeatedGaussianIntegral_zero_right`, `TauCeti.repeatedGaussianIntegral_zero_zero`:
  the value at the origin.
* `TauCeti.repeatedGaussianIntegral_ofReal`, `TauCeti.repeatedGaussianIntegral_ofReal_im`,
  `TauCeti.repeatedGaussianIntegral_ofReal_pos`: the real integral on the real line, its reality
  and positivity.
* `TauCeti.iteratedDeriv_repeatedGaussianIntegral`,
  `TauCeti.iteratedDeriv_re_repeatedGaussianIntegral`: `(d/dz)ᵏ Hh_{n+k} = (-1)ᵏ Hh_n`, and its
  real-line form.
* `TauCeti.iteratedDeriv_cexp_mul_repeatedGaussianIntegral`,
  `TauCeti.iteratedDeriv_exp_mul_re_repeatedGaussianIntegral`: the derivatives of the weighted
  functions `e^{z²/2} Hh_n(z)` and `e^{x²/2} Hh_n(x)`.
* `TauCeti.repeatedGaussianIntegral_zero_ofReal_eq_erfc`: `Hh₀(x) = √(π/2) erfc(x/√2)` for real
  `x`, with `TauCeti.Real.erfc`.

## Implementation notes

In the Laplace form, the derivative comes from the half-line Gaussian–Laplace integrals of
`TauCeti.Analysis.SpecialFunctions.Gaussian.LaplaceIntegral`. Both recurrences come from
integrating the derivative of `t ↦ w(t) e^{-(z+t)²/2}` over `(0, ∞)` for the weight
`w(t) = tᵏ/k!`, which gives minus its value at `t = 0`. Differentiating the Gaussian factor
contributes `-(z Hh_k(z) + (k + 1) Hh_{k+1}(z))` in either case; the weight contributes `0` for
`k = 0` and `Hh_n(z)` for `k = n + 1`. The `erfc` form of `Hh₀` comes from the Gaussian law of
mean `-x` and variance `1`: `Hh₀(x)` is `√(2π)` times the probability that it exceeds `0`. The
real-line derivative ladders are the real parts of the complex ones
(`Differentiable.iteratedDeriv_re_comp_ofReal`).

## References

* *NIST Digital Library of Mathematical Functions*, [§12.7(ii)](https://dlmf.nist.gov/12.7.ii)
  and [§7.18](https://dlmf.nist.gov/7.18).
-/

public section

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Nat Real Topology

namespace TauCeti

/-- The **repeated Gaussian integral** `Hh_n(z) = ∫₀^∞ tⁿ/n! e^{-(z+t)²/2} dt`, indexed by
`n : ℕ`; DLMF 12.7.7 writes the parabolic cylinder function `U(n + ½, z)` as `e^{z²/4} Hh_n(z)`.
The integral runs along the horizontal ray `z + t`, `t ≥ 0`. The notation `Hh_{-1}(z)`
abbreviates `e^{-z²/2}` and is not part of this family. -/
def repeatedGaussianIntegral (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n / n ! * cexp (-((z + t) ^ 2) / 2)

/-- The defining integral of `Hh_n(z)`. -/
theorem repeatedGaussianIntegral_def (n : ℕ) (z : ℂ) :
    repeatedGaussianIntegral n z =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n / n ! * cexp (-((z + t) ^ 2) / 2) := (rfl)

/-- The integrand of `Hh_n(z)` in Laplace form. -/
private theorem pow_div_factorial_mul_cexp_eq (n : ℕ) (z : ℂ) (t : ℝ) :
    (t : ℂ) ^ n / n ! * cexp (-((z + t) ^ 2) / 2) =
      cexp (-z ^ 2 / 2) / n ! * ((t : ℂ) ^ n * cexp (-(1 / 2) * (t : ℂ) ^ 2 - z * t)) := by
  -- Split the exponent so that `Complex.exp_add` factors out `e^{-z²/2}`.
  have hexp : -((z + t) ^ 2) / 2 = -z ^ 2 / 2 + (-(1 / 2) * (t : ℂ) ^ 2 - z * t) := by ring
  rw [hexp, Complex.exp_add]
  ring

/-- On the real line the integrand of `Hh_n(x)` is the cast of a real function. -/
private theorem pow_div_factorial_mul_cexp_ofReal (n : ℕ) (x t : ℝ) :
    (t : ℂ) ^ n / n ! * cexp (-(((x : ℂ) + t) ^ 2) / 2) =
      ((t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2) : ℝ) : ℂ) := by
  push_cast [Complex.ofReal_exp]
  ring_nf

/-- The defining integral of `Hh_n(z)` converges absolutely, for every `n` and `z`. -/
theorem integrableOn_repeatedGaussianIntegral_integrand (n : ℕ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ n / n ! * cexp (-((z + t) ^ 2) / 2)) (Ioi 0) := by
  have h := (integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi (b := 1 / 2) (s := n + 1)
    (by norm_num) (by rw [add_re, natCast_re, one_re]; positivity) z).const_mul
    (cexp (-z ^ 2 / 2) / n !)
  refine IntegrableOn.congr_fun h (fun t _ => ?_) measurableSet_Ioi
  rw [pow_div_factorial_mul_cexp_eq, add_sub_cancel_right, cpow_natCast]

/-- On the real line, the real integrand `t ↦ tⁿ/n! e^{-(x+t)²/2}` of `Hh_n(x)` is integrable on
`(0, ∞)`. -/
theorem integrableOn_repeatedGaussianIntegral_integrand_ofReal (n : ℕ) (x : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2)) (Ioi 0) := by
  refine ((integrableOn_repeatedGaussianIntegral_integrand n x).re).congr_fun (fun t _ => ?_)
    measurableSet_Ioi
  simp only [pow_div_factorial_mul_cexp_ofReal, RCLike.re_to_complex, Complex.ofReal_re]

/-- The Laplace form `Hh_n(z) = e^{-z²/2}/n! ∫₀^∞ tⁿ e^{-t²/2 - zt} dt`. -/
theorem repeatedGaussianIntegral_eq_cexp_div_factorial_mul_integral (n : ℕ) (z : ℂ) :
    repeatedGaussianIntegral n z = cexp (-z ^ 2 / 2) / n ! *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(1 / 2) * (t : ℂ) ^ 2 - z * t) := by
  rw [repeatedGaussianIntegral_def, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => pow_div_factorial_mul_cexp_eq n z t

/-- The derivative `Hh_n′(z) = -(z Hh_n(z) + (n + 1) Hh_{n+1}(z))`, in terms of `Hh_n` and
`Hh_{n+1}`. -/
theorem hasDerivAt_repeatedGaussianIntegral (n : ℕ) (z : ℂ) :
    HasDerivAt (repeatedGaussianIntegral n)
      (-(z * repeatedGaussianIntegral n z + (n + 1) * repeatedGaussianIntegral (n + 1) z)) z := by
  have hL := hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi (b := 1 / 2)
    (s := n + 1) (by norm_num) (by rw [add_re, natCast_re, one_re]; positivity) z
  simp only [add_sub_cancel_right, cpow_natCast] at hL
  have hE : HasDerivAt (fun w : ℂ => cexp (-w ^ 2 / 2)) (cexp (-z ^ 2 / 2) * -z) z := by
    convert Complex.hasDerivAt_cexp_mul_sub_sq (-(1 / 2)) 0 z using 1
    · exact funext fun w => by ring_nf
    · ring_nf
  have hfun : repeatedGaussianIntegral n = fun w => cexp (-w ^ 2 / 2) / n ! *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(1 / 2) * (t : ℂ) ^ 2 - w * t) :=
    funext (repeatedGaussianIntegral_eq_cexp_div_factorial_mul_integral n)
  rw [hfun]
  convert (hE.div_const (n ! : ℂ)).mul hL using 1
  beta_reduce
  rw [repeatedGaussianIntegral_eq_cexp_div_factorial_mul_integral]
  have hcpow : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((n : ℂ) + 1) *
      cexp (-(1 / 2) * (t : ℂ) ^ 2 - z * t)) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (n + 1) * cexp (-(1 / 2) * (t : ℂ) ^ 2 - z * t) := by
    simp_rw [← Nat.cast_add_one, cpow_natCast]
  rw [hcpow, Nat.factorial_succ, Nat.cast_mul]
  field_simp
  push_cast
  ring

/-- Differentiating the Gaussian factor of the integrand of `Hh_k(z)`:
`tᵏ/k! · (-(z + t)) e^{-(z+t)²/2}` is `-(z (tᵏ/k!) + (k + 1) tᵏ⁺¹/(k + 1)!) e^{-(z+t)²/2}`. -/
private theorem pow_div_factorial_mul_cexp_mul_neg_add (k : ℕ) (z : ℂ) (t : ℝ) :
    (t : ℂ) ^ k / k ! * (cexp (-((z + t) ^ 2) / 2) * -(z + t)) =
      -(z * ((t : ℂ) ^ k / k ! * cexp (-((z + t) ^ 2) / 2)) +
        (k + 1) * ((t : ℂ) ^ (k + 1) / (k + 1) ! * cexp (-((z + t) ^ 2) / 2))) := by
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have hk1 : ((k + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast k.succ_ne_zero
  field_simp
  push_cast
  ring

/-- **Integration by parts against the Gaussian.** Let `p` be the derivative of the weight
`t ↦ tᵏ/k!` on the real line, with `p(t) e^{-(z+t)²/2}` integrable on `(0, ∞)`. Then
`∫₀^∞ p(t) e^{-(z+t)²/2} dt = z Hh_k(z) + (k + 1) Hh_{k+1}(z) - 0ᵏ/k! e^{-z²/2}`. -/
private theorem integral_Ioi_mul_cexp_eq (k : ℕ) (z : ℂ) {p : ℝ → ℂ}
    (hp : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (t : ℂ) ^ k / k !) (p t) t)
    (hint : IntegrableOn (fun t => p t * cexp (-((z + t) ^ 2) / 2)) (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), p t * cexp (-((z + t) ^ 2) / 2) =
      z * repeatedGaussianIntegral k z + (k + 1) * repeatedGaussianIntegral (k + 1) z -
        (0 : ℂ) ^ k / k ! * cexp (-z ^ 2 / 2) := by
  set g : ℕ → ℝ → ℂ := fun k t => (t : ℂ) ^ k / k ! * cexp (-((z + t) ^ 2) / 2) with hg
  have hi : ∀ k, IntegrableOn (g k) (Ioi 0) := fun k =>
    integrableOn_repeatedGaussianIntegral_integrand k z
  have hA : IntegrableOn (fun t => z * g k t + (k + 1 : ℂ) * g (k + 1) t) (Ioi 0) :=
    ((hi _).const_mul z).add ((hi _).const_mul _)
  -- The Gaussian factor is the translated quadratic exponential with `a = -1/2`, `b = -z`.
  have hG (w : ℂ) : HasDerivAt (fun v : ℂ => cexp (-((z + v) ^ 2) / 2))
      (cexp (-((z + w) ^ 2) / 2) * -(z + w)) w := by
    convert Complex.hasDerivAt_cexp_mul_sub_sq (-(1 / 2)) (-z) w using 1
    · exact funext fun v => by ring_nf
    · ring_nf
  have hderiv (t : ℝ) : HasDerivAt (g k)
      (p t * cexp (-((z + t) ^ 2) / 2) - (z * g k t + (k + 1) * g (k + 1) t)) t := by
    have h := (hp t).mul (hG t).comp_ofReal
    rw [pow_div_factorial_mul_cexp_mul_neg_add, ← sub_eq_add_neg] at h
    exact h
  have h := integral_Ioi_of_hasDerivAt_of_integrableOn (hderiv 0).continuousAt.continuousWithinAt
    (fun t _ => hderiv t) (hint.sub hA) (hi k)
  rw [integral_sub hint hA, integral_add ((hi _).const_mul z) ((hi _).const_mul _),
    integral_const_mul, integral_const_mul] at h
  simp only [hg, ← repeatedGaussianIntegral_def, Complex.ofReal_zero, add_zero] at h
  linear_combination h

/-- The first recurrence `Hh₁(z) = e^{-z²/2} - z Hh₀(z)`. -/
theorem repeatedGaussianIntegral_one (z : ℂ) :
    repeatedGaussianIntegral 1 z = cexp (-z ^ 2 / 2) - z * repeatedGaussianIntegral 0 z := by
  -- The weight `t⁰/0! = 1` is constant.
  have hp (t : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) ^ 0 / (0 ! : ℕ)) 0 t := by
    simpa using hasDerivAt_const t (1 : ℂ)
  have h := integral_Ioi_mul_cexp_eq 0 z hp (by simp)
  simp only [zero_mul, integral_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    one_mul, zero_add] at h
  linear_combination -h

/-- The three-term recurrence `(n + 2) Hh_{n+2}(z) = Hh_n(z) - z Hh_{n+1}(z)`. -/
theorem repeatedGaussianIntegral_add_two (n : ℕ) (z : ℂ) :
    (n + 2 : ℂ) * repeatedGaussianIntegral (n + 2) z =
      repeatedGaussianIntegral n z - z * repeatedGaussianIntegral (n + 1) z := by
  -- The weight `tⁿ⁺¹/(n + 1)!` has derivative `tⁿ/n!`.
  have hp (t : ℝ) : HasDerivAt (fun t : ℝ => (t : ℂ) ^ (n + 1) / (n + 1 : ℕ) !)
      ((t : ℂ) ^ n / n !) t := by
    have h := ((hasDerivAt_pow (n + 1) (t : ℂ)).div_const ((n + 1 : ℕ) ! : ℂ)).comp_ofReal
    convert h using 1
    have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
    field_simp
  have h := integral_Ioi_mul_cexp_eq (n + 1) z hp
    (integrableOn_repeatedGaussianIntegral_integrand n z)
  rw [← repeatedGaussianIntegral_def, zero_pow n.succ_ne_zero, zero_div, zero_mul,
    sub_zero] at h
  push_cast at h
  linear_combination -h

/-- `Hh₀′(z) = -e^{-z²/2}`. -/
theorem hasDerivAt_repeatedGaussianIntegral_zero (z : ℂ) :
    HasDerivAt (repeatedGaussianIntegral 0) (-cexp (-z ^ 2 / 2)) z := by
  convert hasDerivAt_repeatedGaussianIntegral 0 z using 1
  rw [repeatedGaussianIntegral_one]
  push_cast
  ring

/-- `Hh_{n+1}′(z) = -Hh_n(z)`. -/
theorem hasDerivAt_repeatedGaussianIntegral_succ (n : ℕ) (z : ℂ) :
    HasDerivAt (repeatedGaussianIntegral (n + 1)) (-repeatedGaussianIntegral n z) z := by
  convert hasDerivAt_repeatedGaussianIntegral (n + 1) z using 1
  push_cast
  linear_combination repeatedGaussianIntegral_add_two n z

/-- Each repeated Gaussian integral `Hh_n` is entire. -/
@[fun_prop]
theorem differentiable_repeatedGaussianIntegral (n : ℕ) :
    Differentiable ℂ (repeatedGaussianIntegral n) :=
  fun z => (hasDerivAt_repeatedGaussianIntegral n z).differentiableAt

/-- `Hh₀′ = -e^{-z²/2}`, as a function. -/
@[simp]
theorem deriv_repeatedGaussianIntegral_zero :
    deriv (repeatedGaussianIntegral 0) = fun z => -cexp (-z ^ 2 / 2) :=
  funext fun z => (hasDerivAt_repeatedGaussianIntegral_zero z).deriv

/-- `Hh_{n+1}′ = -Hh_n`, as a function. -/
@[simp]
theorem deriv_repeatedGaussianIntegral_succ (n : ℕ) :
    deriv (repeatedGaussianIntegral (n + 1)) = -repeatedGaussianIntegral n :=
  funext fun z => (hasDerivAt_repeatedGaussianIntegral_succ n z).deriv

/-- On the real line, `Hh_n(x)` is the real integral `∫₀^∞ tⁿ/n! e^{-(x+t)²/2} dt`. -/
theorem repeatedGaussianIntegral_ofReal (n : ℕ) (x : ℝ) :
    repeatedGaussianIntegral n x =
      ((∫ t in Ioi (0 : ℝ), t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2) : ℝ) : ℂ) := by
  rw [repeatedGaussianIntegral_def, ← integral_complex_ofReal]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => pow_div_factorial_mul_cexp_ofReal n x t

/-- `Hh_n(x)` is real for real `x`. -/
@[simp]
theorem repeatedGaussianIntegral_ofReal_im (n : ℕ) (x : ℝ) :
    (repeatedGaussianIntegral n x).im = 0 := by
  rw [repeatedGaussianIntegral_ofReal, Complex.ofReal_im]

/-- **Gaussian decay of `Hh_n`.** For `z = x + iy` with `x ≥ 0`,
`‖Hh_n(z)‖ ≤ e^{(y² - x²)/2} Hh_n(0)`. -/
theorem norm_repeatedGaussianIntegral_le (n : ℕ) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖repeatedGaussianIntegral n z‖ ≤
      Real.exp ((z.im ^ 2 - z.re ^ 2) / 2) * (repeatedGaussianIntegral n 0).re := by
  have hb := (integrableOn_repeatedGaussianIntegral_integrand_ofReal n 0).const_mul
    (Real.exp ((z.im ^ 2 - z.re ^ 2) / 2))
  rw [← Complex.ofReal_zero, repeatedGaussianIntegral_ofReal, Complex.ofReal_re,
    ← integral_const_mul, repeatedGaussianIntegral_def]
  refine (norm_integral_le_integral_norm _).trans (setIntegral_mono_on
    (integrableOn_repeatedGaussianIntegral_integrand n z).norm hb measurableSet_Ioi
    fun t (ht : 0 < t) => ?_)
  have hre : (-((z + t) ^ 2) / 2).re = (z.im ^ 2 - (z.re + t) ^ 2) / 2 := by
    simp only [div_ofNat_re, neg_re, sq, mul_re, add_re, add_im, ofReal_re, ofReal_im, add_zero]
    ring
  simp only [norm_mul, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht.le,
    norm_natCast, Complex.norm_exp, hre]
  rw [mul_left_comm, ← Real.exp_add]
  gcongr
  nlinarith [mul_nonneg hz ht.le]

/-- Gaussian decay of `t ↦ Hh_n(z + t)` along the horizontal ray, beyond `t = |Re z|`. -/
private theorem norm_repeatedGaussianIntegral_add_le (n : ℕ) (z : ℂ) {t : ℝ}
    (ht : |z.re| ≤ t) :
    ‖repeatedGaussianIntegral n (z + t)‖ ≤ Real.exp (z.im ^ 2 / 2) *
      (repeatedGaussianIntegral n 0).re * Real.exp (-(1 / 2) * (t + z.re) ^ 2) := by
  have h := norm_repeatedGaussianIntegral_le n (z := z + t)
    (by simp only [add_re, ofReal_re]; linarith [neg_abs_le z.re])
  simp only [add_re, add_im, ofReal_re, ofReal_im, add_zero] at h
  refine h.trans (le_of_eq ?_)
  rw [mul_right_comm, ← Real.exp_add]
  ring_nf

/-- The function `t ↦ Hh_n(z + t)` along the horizontal ray from `z` is integrable on
`(0, ∞)`. -/
theorem integrableOn_repeatedGaussianIntegral_add (n : ℕ) (z : ℂ) :
    IntegrableOn (fun t : ℝ => repeatedGaussianIntegral n (z + t)) (Ioi 0) := by
  have hc : Continuous fun t : ℝ => repeatedGaussianIntegral n (z + t) :=
    (differentiable_repeatedGaussianIntegral n).continuous.comp (by fun_prop)
  rw [← Ioc_union_Ioi_eq_Ioi (abs_nonneg z.re), integrableOn_union]
  refine ⟨hc.integrableOn_Ioc, ?_⟩
  have hg : Integrable fun t : ℝ => Real.exp (-(1 / 2) * (t + z.re) ^ 2) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).comp_add_right z.re
  have hb := (hg.const_mul (Real.exp (z.im ^ 2 / 2) * (repeatedGaussianIntegral n 0).re))
  refine hb.integrableOn.mono' hc.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t (ht : |z.re| < t) => ?_))
  exact norm_repeatedGaussianIntegral_add_le n z ht.le

/-- **`Hh_{n+1}` is the integral of `Hh_n` along the ray**: `Hh_{n+1}(z) = ∫₀^∞ Hh_n(z + t) dt`. -/
theorem repeatedGaussianIntegral_succ_eq_integral (n : ℕ) (z : ℂ) :
    repeatedGaussianIntegral (n + 1) z =
      ∫ t in Ioi (0 : ℝ), repeatedGaussianIntegral n (z + t) := by
  have hderiv (t : ℝ) : HasDerivAt (fun t : ℝ => repeatedGaussianIntegral (n + 1) (z + t))
      (-repeatedGaussianIntegral n (z + t)) t :=
    ((hasDerivAt_repeatedGaussianIntegral_succ n (z + t)).comp_const_add z t).comp_ofReal
  have h := integral_Ioi_of_hasDerivAt_of_integrableOn (hderiv 0).continuousAt.continuousWithinAt
    (fun t _ => hderiv t)
    (integrableOn_repeatedGaussianIntegral_add n z).neg
    (integrableOn_repeatedGaussianIntegral_add (n + 1) z)
  rw [integral_neg, Complex.ofReal_zero, add_zero, neg_inj] at h
  exact h.symm

/-- The higher-derivative ladder: the `k`-th derivative of `Hh_{n+k}` is `(-1)ᵏ Hh_n`. -/
theorem iteratedDeriv_repeatedGaussianIntegral (n k : ℕ) :
    iteratedDeriv k (repeatedGaussianIntegral (n + k)) =
      fun z : ℂ => (-1) ^ k * repeatedGaussianIntegral n z := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have hk : n + (k + 1) = n + 1 + k := by omega
    rw [iteratedDeriv_succ, hk, ih (n + 1)]
    funext z
    rw [((hasDerivAt_repeatedGaussianIntegral_succ n z).const_mul ((-1 : ℂ) ^ k)).deriv,
      pow_succ]
    ring

/-- On the real line, the `k`-th derivative of `x ↦ Hh_{n+k}(x)` is `(-1)ᵏ Hh_n(x)`; this is the
real-line form of `TauCeti.iteratedDeriv_repeatedGaussianIntegral`. -/
theorem iteratedDeriv_re_repeatedGaussianIntegral (n k : ℕ) :
    iteratedDeriv k (fun x : ℝ => (repeatedGaussianIntegral (n + k) x).re) =
      fun x : ℝ => (-1) ^ k * (repeatedGaussianIntegral n x).re := by
  rw [(differentiable_repeatedGaussianIntegral (n + k)).iteratedDeriv_re_comp_ofReal k,
    iteratedDeriv_repeatedGaussianIntegral]
  funext x
  -- The sign `(-1)ᵏ` is the cast of a real number.
  have hs : (-1 : ℂ) ^ k = (((-1 : ℝ) ^ k : ℝ) : ℂ) := by push_cast; rfl
  rw [hs, Complex.re_ofReal_mul]

/-- The weighted function `e^{z²/2} Hh_n(z)` has derivative `-(n + 1) e^{z²/2} Hh_{n+1}(z)`. -/
theorem hasDerivAt_cexp_mul_repeatedGaussianIntegral (n : ℕ) (z : ℂ) :
    HasDerivAt (fun w => cexp (w ^ 2 / 2) * repeatedGaussianIntegral n w)
      (-((n + 1) * (cexp (z ^ 2 / 2) * repeatedGaussianIntegral (n + 1) z))) z := by
  have hE := ((hasDerivAt_pow 2 z).div_const (2 : ℂ)).cexp
  convert hE.mul (hasDerivAt_repeatedGaussianIntegral n z) using 1
  push_cast
  ring

/-- The `k`-th derivative of the weighted function `e^{z²/2} Hh_n(z)` is
`(-1)ᵏ (n + k)!/n! e^{z²/2} Hh_{n+k}(z)`. -/
theorem iteratedDeriv_cexp_mul_repeatedGaussianIntegral (n k : ℕ) :
    iteratedDeriv k (fun z => cexp (z ^ 2 / 2) * repeatedGaussianIntegral n z) =
      fun z => (-1) ^ k * ((n + k) ! / n ! : ℂ) *
        (cexp (z ^ 2 / 2) * repeatedGaussianIntegral (n + k) z) := by
  induction k with
  | zero =>
    have hn : (n ! : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    simp [hn]
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [((hasDerivAt_cexp_mul_repeatedGaussianIntegral (n + k) z).const_mul
      ((-1) ^ k * ((n + k) ! / n ! : ℂ))).deriv, ← add_assoc, Nat.factorial_succ (n + k)]
    push_cast
    ring

/-- On the real line the weighted function `e^{x²/2} Hh_n(x)` is the real part of its complex
counterpart. -/
private theorem exp_mul_re_repeatedGaussianIntegral (n : ℕ) (x : ℝ) :
    Real.exp (x ^ 2 / 2) * (repeatedGaussianIntegral n x).re =
      (cexp ((x : ℂ) ^ 2 / 2) * repeatedGaussianIntegral n x).re := by
  have hx : cexp ((x : ℂ) ^ 2 / 2) = ((Real.exp (x ^ 2 / 2) : ℝ) : ℂ) := by
    push_cast [Complex.ofReal_exp]
    ring_nf
  rw [hx, Complex.re_ofReal_mul]

/-- On the real line, `x ↦ e^{x²/2} Hh_n(x)` has derivative `-(n + 1) e^{x²/2} Hh_{n+1}(x)`. -/
theorem hasDerivAt_exp_mul_re_repeatedGaussianIntegral (n : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (y ^ 2 / 2) * (repeatedGaussianIntegral n y).re)
      (-((n + 1) * (Real.exp (x ^ 2 / 2) * (repeatedGaussianIntegral (n + 1) x).re))) x := by
  have h := (hasDerivAt_cexp_mul_repeatedGaussianIntegral n x).real_of_complex
  -- The complex factor `n + 1` is the cast of a real number.
  have hc : ((n : ℂ) + 1) = (((n + 1 : ℝ)) : ℂ) := by push_cast; ring
  rw [hc, neg_re, Complex.re_ofReal_mul, ← exp_mul_re_repeatedGaussianIntegral] at h
  simpa only [← exp_mul_re_repeatedGaussianIntegral] using h

/-- On the real line, the `k`-th derivative of `x ↦ e^{x²/2} Hh_n(x)` is
`(-1)ᵏ (n + k)!/n! e^{x²/2} Hh_{n+k}(x)`. -/
theorem iteratedDeriv_exp_mul_re_repeatedGaussianIntegral (n k : ℕ) :
    iteratedDeriv k (fun x : ℝ => Real.exp (x ^ 2 / 2) * (repeatedGaussianIntegral n x).re) =
      fun x => (-1) ^ k * ((n + k) ! / n ! : ℝ) *
        (Real.exp (x ^ 2 / 2) * (repeatedGaussianIntegral (n + k) x).re) := by
  have hd : Differentiable ℂ fun z => cexp (z ^ 2 / 2) * repeatedGaussianIntegral n z := by
    fun_prop
  simp only [exp_mul_re_repeatedGaussianIntegral]
  rw [hd.iteratedDeriv_re_comp_ofReal k, iteratedDeriv_cexp_mul_repeatedGaussianIntegral]
  funext x
  -- The coefficient `(-1)ᵏ (n + k)!/n!` is the cast of a real number.
  have hc : (-1 : ℂ) ^ k * ((n + k) ! / n ! : ℂ) =
      (((-1) ^ k * ((n + k) ! / n ! : ℝ) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hc, Complex.re_ofReal_mul]

/-- The value at the origin `Hh_n(0) = 2^{(n-1)/2} Γ((n + 1)/2) / n!`. -/
theorem repeatedGaussianIntegral_zero_right (n : ℕ) :
    repeatedGaussianIntegral n 0 =
      ((2 : ℝ) ^ (((n : ℝ) - 1) / 2) * Real.Gamma ((n + 1) / 2) / n ! : ℝ) := by
  have h := TauCeti.integral_Ioi_pow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) n
  -- The prefactor `1 / (2 · (1/2)^{(n+1)/2})` of the Gaussian moment integral is `2^{(n-1)/2}`.
  have h2 : ((2 : ℝ) ^ (((n : ℝ) - 1) / 2)) = (2 * (1 / 2 : ℝ) ^ (((n : ℝ) + 1) / 2))⁻¹ := by
    rw [one_div, Real.inv_rpow zero_le_two, mul_inv, inv_inv, ← Real.rpow_neg_one 2,
      ← Real.rpow_add two_pos]
    ring_nf
  rw [← Complex.ofReal_zero, repeatedGaussianIntegral_ofReal, h2, ← div_eq_inv_mul, ← h,
    ← integral_div]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  -- Match the exponent `-(1 / 2) t²` of the Gaussian moment integral.
  have ht : -((0 + t) ^ 2) / 2 = -(1 / 2) * t ^ 2 := by ring
  rw [ht]
  ring

/-- Reality and positivity of `Hh_n(x)` for real `x`. -/
theorem repeatedGaussianIntegral_ofReal_pos (n : ℕ) (x : ℝ) :
    (repeatedGaussianIntegral n x).im = 0 ∧ 0 < (repeatedGaussianIntegral n x).re := by
  refine ⟨repeatedGaussianIntegral_ofReal_im n x, ?_⟩
  rw [repeatedGaussianIntegral_ofReal, Complex.ofReal_re]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2) := fun t ht =>
    mul_pos (div_pos (pow_pos ht n) (mod_cast n.factorial_pos)) (Real.exp_pos _)
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpos t ht).le)
    (integrableOn_repeatedGaussianIntegral_integrand_ofReal n x)]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi 0) fun t ht => ⟨(hpos t ht).ne', ht⟩)
  simp

/-- On the real line, `Hh₀(x) = √(π/2) erfc(x/√2)`: `Hh₀(x)` is `√(2π)` times the probability
of exceeding `0` under the Gaussian law of mean `-x` and variance `1`. -/
theorem repeatedGaussianIntegral_zero_ofReal_eq_erfc (x : ℝ) :
    repeatedGaussianIntegral 0 x = ((√(π / 2) * TauCeti.Real.erfc (x / √2) : ℝ) : ℂ) := by
  -- The integrand of `Hh₀(x)` is `√(2π)` times the Gaussian density of mean `-x`, variance `1`.
  have hpdf (t : ℝ) : t ^ 0 / (0 ! : ℕ) * Real.exp (-((x + t) ^ 2) / 2) =
      √(2 * π) * ProbabilityTheory.gaussianPDFReal (-x) 1 t := by
    rw [← zero_sub x, ← ProbabilityTheory.gaussianPDFReal_add,
      TauCeti.Probability.gaussianPDFReal_zero_one, mul_inv_cancel_left₀ (by positivity),
      add_comm t x]
    ring_nf
  -- The density integral over `(0, ∞)` is the Gaussian mass of `(0, ∞)`.
  have hmass : ∫ t in Ioi (0 : ℝ), ProbabilityTheory.gaussianPDFReal (-x) 1 t =
      (ProbabilityTheory.gaussianReal (-x) 1).real (Ioi 0) := by
    rw [measureReal_def, ProbabilityTheory.gaussianReal_apply_eq_integral _ one_ne_zero,
      ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi fun t _ =>
        ProbabilityTheory.gaussianPDFReal_nonneg _ _ t)]
  -- The square-root scaling `√(2π) / 2 = √(π/2)`.
  have hscale (y : ℝ) : √(2 * π) * (y / 2) = √(π / 2) * y := by
    rw [Real.sqrt_div' π zero_le_two, Real.sqrt_mul zero_le_two]
    have hs2 : (√2 : ℝ) ≠ 0 := by positivity
    field_simp
    rw [Real.sq_sqrt zero_le_two]
    ring
  rw [repeatedGaussianIntegral_ofReal]
  congr 1
  simp_rw [hpdf]
  rw [integral_const_mul, hmass,
    TauCeti.Probability.measureReal_Ioi_gaussianReal _ one_ne_zero, hscale]
  simp

/-- `Hh₀(0) = √(π/2)`. -/
@[simp]
theorem repeatedGaussianIntegral_zero_zero : repeatedGaussianIntegral 0 0 = (√(π / 2) : ℝ) := by
  rw [← Complex.ofReal_zero, repeatedGaussianIntegral_zero_ofReal_eq_erfc, zero_div,
    TauCeti.Real.erfc_zero, mul_one]

end TauCeti
