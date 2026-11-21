/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Erf.Basic

import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.Analysis.SpecialFunctions.Gaussian.Concentration
import TauCeti.Analysis.SpecialFunctions.Gaussian.LaplaceIntegral
import TauCeti.Probability.Distributions.Gaussian.Cdf

/-!
# Repeated integrals of the Gaussian

This file defines the repeated Gaussian integrals (DLMF 12.7.7)

$$
\mathrm{Hh}_n(z) = \int_0^\infty \frac{t^n}{n!}\, e^{-(z+t)^2/2}\, dt, \qquad n \in \mathbb{N},
$$

for complex `z`, and develops their basic theory. The integral runs along the horizontal ray
`z + t`, `t ≥ 0`, from `z` towards `+∞`. Writing `Hh_{-1}(z)` for `e^{-z²/2}`, the integral `Hh_n`
is the `(n + 1)`-fold repeated integral of `Hh_{-1}` along this ray. The integrals converge
absolutely for every `n` and `z`, and each `Hh_n` is entire with
`Hh₀′(z) = -e^{-z²/2}` and `Hh_{n+1}′(z) = -Hh_n(z)`. They satisfy
`Hh₁(z) = e^{-z²/2} - z Hh₀(z)` and the three-term recurrence
`(n + 2) Hh_{n+2}(z) = Hh_n(z) - z Hh_{n+1}(z)`. At the origin
`Hh_n(0) = 2^{(n-1)/2} Γ((n + 1)/2) / n!`, and `Hh_n(x)` is real and positive for real `x`,
with `Hh₀(x) = √(π/2) erfc(x/√2)`. On the real line the `k`-th derivative of `Hh_{n+k}` is
`(-1)ᵏ Hh_n`.

## Main declarations

* `TauCeti.repeatedGaussianIntegral`: the repeated Gaussian integral `Hh_n(z)`.
* `TauCeti.integrableOn_repeatedGaussianIntegral_integrand`: the defining integral converges
  absolutely.
* `TauCeti.repeatedGaussianIntegral_eq_cexp_mul_integral`: the Laplace form
  `Hh_n(z) = e^{-z²/2}/n! ∫₀^∞ tⁿ e^{-t²/2 - zt} dt`.
* `TauCeti.hasDerivAt_repeatedGaussianIntegral_zero`,
  `TauCeti.hasDerivAt_repeatedGaussianIntegral_succ`,
  `TauCeti.differentiable_repeatedGaussianIntegral`: the derivatives, and entirety.
* `TauCeti.repeatedGaussianIntegral_one`, `TauCeti.repeatedGaussianIntegral_add_two`: the
  recurrences.
* `TauCeti.repeatedGaussianIntegral_zero_right`, `TauCeti.repeatedGaussianIntegral_zero_zero`:
  the value at the origin.
* `TauCeti.repeatedGaussianIntegral_ofReal`, `TauCeti.repeatedGaussianIntegral_ofReal_im`,
  `TauCeti.repeatedGaussianIntegral_ofReal_pos`: the real integral on the real line, its reality
  and positivity.
* `TauCeti.iteratedDeriv_re_repeatedGaussianIntegral`: on the real line,
  `(d/dx)ᵏ Hh_{n+k}(x) = (-1)ᵏ Hh_n(x)`.
* `TauCeti.repeatedGaussianIntegral_zero_ofReal_eq_erfc`: `Hh₀(x) = √(π/2) erfc(x/√2)` for real
  `x`, with `TauCeti.Real.erfc`.

## Implementation notes

In the Laplace form, the derivative comes from the half-line Gaussian–Laplace integrals of
`TauCeti.Analysis.SpecialFunctions.Gaussian.LaplaceIntegral`. Both recurrences come from
integrating the derivative of `t ↦ tᵏ/k! e^{-(z+t)²/2}` over `(0, ∞)`, which gives minus its
value at `t = 0`. For `k = 0` this derivative is `-(z + t) e^{-(z+t)²/2}` and the boundary term
`e^{-z²/2}` produces the first recurrence; for `k = n + 1` the boundary term vanishes and the
derivative gives the three-term recurrence. The `erfc` form of `Hh₀` is the upper tail of the
Gaussian law of mean `-x` and variance `1`.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.7(ii)](https://dlmf.nist.gov/12.7.ii).
-/

public section

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Nat Real Topology

namespace TauCeti

/-- The **repeated Gaussian integral** `Hh_n(z) = ∫₀^∞ tⁿ/n! e^{-(z+t)²/2} dt` (DLMF 12.7.7),
indexed by `n : ℕ`. The integral runs along the horizontal ray `z + t`, `t ≥ 0`. The notation
`Hh_{-1}(z)` abbreviates `e^{-z²/2}` and is not part of this family. -/
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

/-- The complex power `t ^ ((n + 1) - 1)` of the Gaussian–Laplace integrals is `t ^ n`. -/
private theorem cpow_natCast_add_one_sub_one (n : ℕ) (t : ℝ) :
    (t : ℂ) ^ ((n + 1 : ℂ) - 1) = (t : ℂ) ^ n := by
  rw [add_sub_cancel_right, cpow_natCast]

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
  rw [pow_div_factorial_mul_cexp_eq, cpow_natCast_add_one_sub_one]

/-- The Laplace form `Hh_n(z) = e^{-z²/2}/n! ∫₀^∞ tⁿ e^{-t²/2 - zt} dt`. -/
theorem repeatedGaussianIntegral_eq_cexp_mul_integral (n : ℕ) (z : ℂ) :
    repeatedGaussianIntegral n z = cexp (-z ^ 2 / 2) / n ! *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(1 / 2) * (t : ℂ) ^ 2 - z * t) := by
  rw [repeatedGaussianIntegral_def, ← integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => pow_div_factorial_mul_cexp_eq n z t

/-- The derivative `Hh_n′(z) = -(z Hh_n(z) + (n + 1) Hh_{n+1}(z))`, before the recurrences. -/
theorem hasDerivAt_repeatedGaussianIntegral (n : ℕ) (z : ℂ) :
    HasDerivAt (repeatedGaussianIntegral n)
      (-(z * repeatedGaussianIntegral n z + (n + 1) * repeatedGaussianIntegral (n + 1) z)) z := by
  have hL := hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi (b := 1 / 2)
    (s := n + 1) (by norm_num) (by rw [add_re, natCast_re, one_re]; positivity) z
  simp only [cpow_natCast_add_one_sub_one] at hL
  have hE : HasDerivAt (fun w : ℂ => cexp (-w ^ 2 / 2)) (cexp (-z ^ 2 / 2) * -z) z := by
    simpa only [zero_add] using Complex.hasDerivAt_cexp_neg_add_sq_div_two 0 z
  have hfun : repeatedGaussianIntegral n = fun w => cexp (-w ^ 2 / 2) / n ! *
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ n * cexp (-(1 / 2) * (t : ℂ) ^ 2 - w * t) :=
    funext (repeatedGaussianIntegral_eq_cexp_mul_integral n)
  rw [hfun]
  convert (hE.div_const (n ! : ℂ)).mul hL using 1
  beta_reduce
  rw [repeatedGaussianIntegral_eq_cexp_mul_integral]
  have hcpow : (∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((n : ℂ) + 1) *
      cexp (-(1 / 2) * (t : ℂ) ^ 2 - z * t)) =
      ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (n + 1) * cexp (-(1 / 2) * (t : ℂ) ^ 2 - z * t) := by
    simp_rw [← Nat.cast_add_one, cpow_natCast]
  rw [hcpow, Nat.factorial_succ, Nat.cast_mul]
  field_simp
  push_cast
  ring

/-- The integral over `(0, ∞)` of the derivative of the weighted Gaussian
`t ↦ tᵏ/k! e^{-(z+t)²/2}` is minus its value `0ᵏ/k! e^{-z²/2}` at `t = 0`. The derivative is
given as any integrable function `f` equal to it pointwise. -/
private theorem integral_Ioi_deriv_pow_div_factorial_mul_cexp (k : ℕ) (z : ℂ) {f : ℝ → ℂ}
    (hf : ∀ t : ℝ, f t = (k : ℂ) * (t : ℂ) ^ (k - 1) / k ! * cexp (-((z + t) ^ 2) / 2) +
      (t : ℂ) ^ k / k ! * (cexp (-((z + t) ^ 2) / 2) * -(z + t)))
    (hint : IntegrableOn f (Ioi 0)) :
    ∫ t in Ioi (0 : ℝ), f t = -((0 : ℂ) ^ k / k ! * cexp (-z ^ 2 / 2)) := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ),
      HasDerivAt (fun t : ℝ => (t : ℂ) ^ k / k ! * cexp (-((z + t) ^ 2) / 2)) (f t) t :=
    fun t _ => by
    have hp : HasDerivAt (fun w : ℂ => w ^ k / (k ! : ℂ)) ((k : ℂ) * (t : ℂ) ^ (k - 1) / k !) t :=
      by simpa using (hasDerivAt_pow k (t : ℂ)).div_const (k ! : ℂ)
    rw [hf t]
    exact (hp.mul (Complex.hasDerivAt_cexp_neg_add_sq_div_two z t)).comp_ofReal
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun t ht => hderiv t (le_of_lt ht)) hint
      (integrableOn_repeatedGaussianIntegral_integrand k z))
  rw [h, zero_sub, Complex.ofReal_zero, add_zero]

/-- The first recurrence `Hh₁(z) = e^{-z²/2} - z Hh₀(z)`. -/
theorem repeatedGaussianIntegral_one (z : ℂ) :
    repeatedGaussianIntegral 1 z = cexp (-z ^ 2 / 2) - z * repeatedGaussianIntegral 0 z := by
  have hi := integrableOn_repeatedGaussianIntegral_integrand
  have hint : IntegrableOn (fun t : ℝ => -(z * ((t : ℂ) ^ 0 / (0 ! : ℕ) *
      cexp (-((z + t) ^ 2) / 2)) + (t : ℂ) ^ 1 / (1 ! : ℕ) * cexp (-((z + t) ^ 2) / 2))) (Ioi 0) :=
    (((hi 0 z).const_mul z).add (hi 1 z)).neg
  have h := integral_Ioi_deriv_pow_div_factorial_mul_cexp 0 z (fun t => ?_) hint
  swap
  · simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one,
      Nat.cast_zero, div_one, one_mul, zero_mul, zero_add]
    ring
  rw [integral_neg, integral_add ((hi 0 z).const_mul z) (hi 1 z), integral_const_mul] at h
  simp only [← repeatedGaussianIntegral_def, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    one_mul] at h
  have h0 : repeatedGaussianIntegral 0 z = ∫ t in Ioi (0 : ℝ), cexp (-((z + t) ^ 2) / 2) := by
    simp [repeatedGaussianIntegral_def]
  linear_combination -h + z * h0

/-- The three-term recurrence `(n + 2) Hh_{n+2}(z) = Hh_n(z) - z Hh_{n+1}(z)`. -/
theorem repeatedGaussianIntegral_add_two (n : ℕ) (z : ℂ) :
    (n + 2 : ℂ) * repeatedGaussianIntegral (n + 2) z =
      repeatedGaussianIntegral n z - z * repeatedGaussianIntegral (n + 1) z := by
  set g : ℕ → ℝ → ℂ := fun k t => (t : ℂ) ^ k / k ! * cexp (-((z + t) ^ 2) / 2) with hg
  have hi : ∀ k, IntegrableOn (g k) (Ioi 0) := fun k =>
    integrableOn_repeatedGaussianIntegral_integrand k z
  have hA : IntegrableOn (fun t => z * g (n + 1) t + (n + 2 : ℂ) * g (n + 2) t) (Ioi 0) :=
    ((hi _).const_mul z).add ((hi _).const_mul _)
  have h := integral_Ioi_deriv_pow_div_factorial_mul_cexp (n + 1) z
    (f := fun t => g n t - (z * g (n + 1) t + (n + 2) * g (n + 2) t))
    (fun t => by
      have h1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
      have h2 : (n + 1 + 1 : ℂ) ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
      simp only [hg, Nat.add_sub_cancel]
      push_cast [Nat.factorial_succ]
      field_simp
      ring)
    ((hi n).sub hA)
  rw [integral_sub (hi n) hA, integral_add ((hi _).const_mul z) ((hi _).const_mul _),
    integral_const_mul, integral_const_mul] at h
  simp only [hg, ← repeatedGaussianIntegral_def, zero_pow (Nat.succ_ne_zero n), zero_div,
    zero_mul, neg_zero] at h
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

/-- On the real line, the `k`-th derivative of `x ↦ Hh_{n+k}(x)` is `(-1)ᵏ Hh_n(x)`. -/
theorem iteratedDeriv_re_repeatedGaussianIntegral (n k : ℕ) :
    iteratedDeriv k (fun x : ℝ => (repeatedGaussianIntegral (n + k) x).re) =
      fun x : ℝ => (-1) ^ k * (repeatedGaussianIntegral n x).re := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have hk : n + (k + 1) = n + 1 + k := by omega
    rw [iteratedDeriv_succ, hk, ih (n + 1)]
    funext x
    rw [((hasDerivAt_repeatedGaussianIntegral_succ n x).real_of_complex.const_mul
      ((-1 : ℝ) ^ k)).deriv, neg_re, pow_succ]
    ring

/-- The value at the origin `Hh_n(0) = 2^{(n-1)/2} Γ((n + 1)/2) / n!`. -/
theorem repeatedGaussianIntegral_zero_right (n : ℕ) :
    repeatedGaussianIntegral n 0 =
      ((2 : ℝ) ^ (((n : ℝ) - 1) / 2) * Real.Gamma ((n + 1) / 2) / n ! : ℝ) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := n) (b := 1 / 2)
    (by norm_num) (by have := n.cast_nonneg (α := ℝ); linarith) (by norm_num)
  have hexp : ((n : ℝ) - 1) / 2 = ((n : ℝ) + 1) / 2 - 1 := by ring
  have h2 : (2 : ℝ) ^ (((n : ℝ) - 1) / 2) = (1 / 2 : ℝ) ^ (-((n : ℝ) + 1) / 2) * (1 / 2) := by
    rw [hexp, Real.rpow_sub_one two_ne_zero, one_div, Real.inv_rpow zero_le_two,
      ← Real.rpow_neg zero_le_two, neg_div, neg_neg]
    ring
  rw [← Complex.ofReal_zero, repeatedGaussianIntegral_ofReal, h2, ← h, ← integral_div]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  -- Match the exponent `-(1 / 2) t²` of the Gaussian moment integral.
  have ht : -((0 + t) ^ 2) / 2 = -(1 / 2) * t ^ 2 := by ring
  rw [Real.rpow_natCast, Real.rpow_two, ht]
  ring

/-- `Hh₀(0) = √(π/2)`. -/
@[simp]
theorem repeatedGaussianIntegral_zero_zero : repeatedGaussianIntegral 0 0 = (√(π / 2) : ℝ) := by
  rw [repeatedGaussianIntegral_zero_right]
  congr 1
  norm_num
  rw [Real.Gamma_one_half_eq, Real.sqrt_eq_rpow 2, Real.rpow_neg zero_le_two, inv_mul_eq_div]

/-- Reality and positivity of `Hh_n(x)` for real `x`. -/
theorem repeatedGaussianIntegral_ofReal_pos (n : ℕ) (x : ℝ) :
    (repeatedGaussianIntegral n x).im = 0 ∧ 0 < (repeatedGaussianIntegral n x).re := by
  refine ⟨repeatedGaussianIntegral_ofReal_im n x, ?_⟩
  rw [repeatedGaussianIntegral_ofReal, Complex.ofReal_re]
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2) := fun t ht =>
    mul_pos (div_pos (pow_pos ht n) (mod_cast n.factorial_pos)) (Real.exp_pos _)
  have hint : IntegrableOn (fun t : ℝ => t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2)) (Ioi 0) := by
    refine ((integrableOn_repeatedGaussianIntegral_integrand n x).re).congr_fun (fun t _ => ?_)
      measurableSet_Ioi
    simp only [pow_div_factorial_mul_cexp_ofReal, RCLike.re_to_complex, Complex.ofReal_re]
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpos t ht).le) hint]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi 0) fun t ht => ⟨(hpos t ht).ne', ht⟩)
  simp

/-- On the real line, `Hh₀(x) = √(π/2) erfc(x/√2)`: up to the factor `√(2π)`, `Hh₀(x)` is the
upper tail beyond `0` of the Gaussian law of mean `-x` and variance `1`. -/
theorem repeatedGaussianIntegral_zero_ofReal_eq_erfc (x : ℝ) :
    repeatedGaussianIntegral 0 x = ((√(π / 2) * TauCeti.Real.erfc (x / √2) : ℝ) : ℂ) := by
  have hv : (1 : NNReal) ≠ 0 := one_ne_zero
  have htail := TauCeti.Probability.measureReal_Ioi_gaussianReal (-x) hv 0
  rw [measureReal_def, ProbabilityTheory.gaussianReal_apply_eq_integral (-x) hv,
    ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
      fun t _ => ProbabilityTheory.gaussianPDFReal_nonneg _ _ t)] at htail
  -- The integrand of `Hh₀(x)` is `√(2π)` times the Gaussian density of mean `-x`, variance `1`.
  have hpdf (t : ℝ) : t ^ 0 / (0 ! : ℕ) * Real.exp (-((x + t) ^ 2) / 2) =
      √(2 * π) * ProbabilityTheory.gaussianPDFReal (-x) 1 t := by
    have hs : √(2 * π) ≠ 0 := by positivity
    rw [ProbabilityTheory.gaussianPDFReal, NNReal.coe_one, mul_one, sub_neg_eq_add, add_comm t x]
    field_simp
    simp
  rw [repeatedGaussianIntegral_ofReal]
  congr 1
  simp_rw [hpdf]
  rw [integral_const_mul, htail, zero_sub, neg_neg, NNReal.coe_one, mul_one,
    Real.sqrt_div' π zero_le_two, Real.sqrt_mul zero_le_two]
  have hs2 : (√2 : ℝ) ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt zero_le_two]
  ring

end TauCeti
