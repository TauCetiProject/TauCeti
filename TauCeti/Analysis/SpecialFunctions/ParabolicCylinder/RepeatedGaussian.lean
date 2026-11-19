/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Analysis.SpecialFunctions.Erf.Basic

import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Gamma
import TauCeti.Analysis.SpecialFunctions.Gaussian.LaplaceIntegral

/-!
# Repeated integrals of the Gaussian

This file defines the repeated Gaussian integrals (DLMF 12.7.7)

$$
\mathrm{Hh}_n(z) = \int_0^\infty \frac{t^n}{n!}\, e^{-(z+t)^2/2}\, dt, \qquad n \in \mathbb{N},
$$

for complex `z`, and develops their basic theory. Writing `Hh_{-1}(z)` for `e^{-z²/2}`, the
integral `Hh_n` is the `(n + 1)`-fold repeated integral of `Hh_{-1}` from `z` to `∞`. The
integrals converge absolutely for every `n` and `z`, and each `Hh_n` is entire with
`Hh₀′(z) = -e^{-z²/2}` and `Hh_{n+1}′(z) = -Hh_n(z)`. They satisfy
`Hh₁(z) = e^{-z²/2} - z Hh₀(z)` and the three-term recurrence
`(n + 2) Hh_{n+2}(z) = Hh_n(z) - z Hh_{n+1}(z)`. At the origin
`Hh_n(0) = 2^{(n-1)/2} Γ((n + 1)/2) / n!`, and `Hh_n(x)` is real and positive for real `x`,
with `Hh₀(x) = √(π/2) erfc(x/√2)`.

## Main declarations

* `TauCeti.repeatedGaussianIntegral`: the repeated Gaussian integral `Hh_n(z)`.
* `TauCeti.repeatedGaussianIntegral_convergent`: the defining integral converges absolutely.
* `TauCeti.repeatedGaussianIntegral_eq_cexp_mul_integral`: the Laplace form
  `Hh_n(z) = e^{-z²/2}/n! ∫₀^∞ tⁿ e^{-t²/2 - zt} dt`.
* `TauCeti.hasDerivAt_repeatedGaussianIntegral_zero`,
  `TauCeti.hasDerivAt_repeatedGaussianIntegral_succ`,
  `TauCeti.differentiable_repeatedGaussianIntegral`: the derivatives, and entirety.
* `TauCeti.repeatedGaussianIntegral_one`, `TauCeti.repeatedGaussianIntegral_add_two`: the
  recurrences.
* `TauCeti.repeatedGaussianIntegral_zero_right`, `TauCeti.repeatedGaussianIntegral_zero_zero`:
  the value at the origin.
* `TauCeti.repeatedGaussianIntegral_ofReal`, `TauCeti.repeatedGaussianIntegral_ofReal_pos`:
  the real integral on the real line, its reality and positivity.
* `TauCeti.repeatedGaussianIntegral_zero_ofReal_eq_erfc`: `Hh₀(x) = √(π/2) erfc(x/√2)` for real
  `x`, with `TauCeti.Real.erfc`.

## Implementation notes

In the Laplace form, the derivative comes from the half-line Gaussian–Laplace integrals of
`TauCeti.Analysis.SpecialFunctions.Gaussian.LaplaceIntegral`. The recurrences come from
integrating the derivative of `t ↦ t^{n+1}/(n+1)! e^{-(z+t)²/2}` over `(0, ∞)`. The `erfc` form
of `Hh₀` follows from equal derivatives and equal values at the origin.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.7(ii)](https://dlmf.nist.gov/12.7.ii).
-/

public section

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Nat Real Topology

namespace TauCeti

/-- The **repeated Gaussian integral** `Hh_n(z) = ∫₀^∞ tⁿ/n! e^{-(z+t)²/2} dt` (DLMF 12.7.7),
indexed by `n : ℕ`. The notation `Hh_{-1}(z)` abbreviates `e^{-z²/2}` and is not part of this
family. -/
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
  rw [show -((z + t) ^ 2) / 2 = -z ^ 2 / 2 + (-(1 / 2) * (t : ℂ) ^ 2 - z * t) by ring,
    Complex.exp_add]
  ring

/-- The complex power `t ^ ((n + 1) - 1)` of the Gaussian–Laplace integrals is `t ^ n`. -/
private theorem cpow_natCast_add_one_sub_one (n : ℕ) (t : ℝ) :
    (t : ℂ) ^ ((n + 1 : ℂ) - 1) = (t : ℂ) ^ n := by
  rw [add_sub_cancel_right, cpow_natCast]

/-- The defining integral of `Hh_n(z)` converges absolutely, for every `n` and `z`. -/
theorem repeatedGaussianIntegral_convergent (n : ℕ) (z : ℂ) :
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
  have hE : HasDerivAt (fun w : ℂ => cexp (-w ^ 2 / 2)) (cexp (-z ^ 2 / 2) * (-z)) z := by
    have h : HasDerivAt (fun w : ℂ => -w ^ 2 / 2) (-z) z := by
      convert (hasDerivAt_pow 2 z).fun_neg.div_const 2 using 1
      ring
    exact h.cexp
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

/-- The Gaussian `w ↦ e^{-(z+w)²/2}` has derivative `-(z + w) e^{-(z+w)²/2}`. -/
private theorem hasDerivAt_cexp_neg_add_sq_div_two (z w : ℂ) :
    HasDerivAt (fun v : ℂ => cexp (-((z + v) ^ 2) / 2)) (cexp (-((z + w) ^ 2) / 2) * -(z + w))
      w := by
  have h : HasDerivAt (fun v : ℂ => -((z + v) ^ 2) / 2) (-(z + w)) w := by
    convert (((hasDerivAt_id' w).const_add z).fun_pow 2).fun_neg.div_const 2 using 1
    push_cast
    ring
  exact h.cexp

/-- The first recurrence `Hh₁(z) = e^{-z²/2} - z Hh₀(z)`. -/
theorem repeatedGaussianIntegral_one (z : ℂ) :
    repeatedGaussianIntegral 1 z = cexp (-z ^ 2 / 2) - z * repeatedGaussianIntegral 0 z := by
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (fun t : ℝ => cexp (-((z + t) ^ 2) / 2))
      (-(z * ((t : ℂ) ^ 0 / (0 ! : ℕ) * cexp (-((z + t) ^ 2) / 2)) +
        (t : ℂ) ^ 1 / (1 ! : ℕ) * cexp (-((z + t) ^ 2) / 2))) t := fun t _ => by
    convert (hasDerivAt_cexp_neg_add_sq_div_two z t).comp_ofReal using 1
    simp only [pow_zero, pow_one, Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, div_one,
      one_mul]
    ring
  have hint := (((repeatedGaussianIntegral_convergent 0 z).const_mul z).add
    (repeatedGaussianIntegral_convergent 1 z)).neg
  have hF : IntegrableOn (fun t : ℝ => cexp (-((z + t) ^ 2) / 2)) (Ioi 0) :=
    (repeatedGaussianIntegral_convergent 0 z).congr_fun (fun t _ => by simp) measurableSet_Ioi
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun t ht => hderiv t (le_of_lt ht)) hint hF)
  rw [integral_neg, integral_add ((repeatedGaussianIntegral_convergent 0 z).const_mul z)
    (repeatedGaussianIntegral_convergent 1 z), integral_const_mul] at h
  simp only [← repeatedGaussianIntegral_def, Complex.ofReal_zero, add_zero] at h
  linear_combination -h

/-- The three-term recurrence `(n + 2) Hh_{n+2}(z) = Hh_n(z) - z Hh_{n+1}(z)`. -/
theorem repeatedGaussianIntegral_add_two (n : ℕ) (z : ℂ) :
    (n + 2 : ℂ) * repeatedGaussianIntegral (n + 2) z =
      repeatedGaussianIntegral n z - z * repeatedGaussianIntegral (n + 1) z := by
  set g : ℕ → ℝ → ℂ := fun k t => (t : ℂ) ^ k / k ! * cexp (-((z + t) ^ 2) / 2) with hg
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (g (n + 1))
      (g n t - (z * g (n + 1) t + (n + 2) * g (n + 2) t)) t := fun t _ => by
    have hp : HasDerivAt (fun w : ℂ => w ^ (n + 1) / ((n + 1) ! : ℕ))
        (((n + 1 : ℕ) : ℂ) * (t : ℂ) ^ n / ((n + 1) ! : ℕ)) t := by
      simpa using (hasDerivAt_pow (n + 1) (t : ℂ)).div_const (((n + 1) ! : ℕ) : ℂ)
    convert (hp.mul (hasDerivAt_cexp_neg_add_sq_div_two z t)).comp_ofReal using 1
    have h1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    have h2 : (n + 1 + 1 : ℂ) ≠ 0 := by exact_mod_cast (n + 1).succ_ne_zero
    simp only [hg]
    push_cast [Nat.factorial_succ]
    field_simp
    ring
  have hi : ∀ k, IntegrableOn (g k) (Ioi 0) := fun k => repeatedGaussianIntegral_convergent k z
  have hA : IntegrableOn (fun t => z * g (n + 1) t + (n + 2 : ℂ) * g (n + 2) t) (Ioi 0) :=
    ((hi _).const_mul z).add ((hi _).const_mul _)
  have hint := (hi n).sub hA
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint
    (tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (fun t ht => hderiv t (le_of_lt ht)) hint
      (hi (n + 1)))
  rw [integral_sub (hi n) hA, integral_add ((hi _).const_mul z) ((hi _).const_mul _),
    integral_const_mul, integral_const_mul] at h
  simp only [hg, ← repeatedGaussianIntegral_def, Complex.ofReal_zero, zero_pow
    (Nat.succ_ne_zero n), zero_div, zero_mul, sub_zero] at h
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
  push_cast
  rfl

/-- The value at the origin `Hh_n(0) = 2^{(n-1)/2} Γ((n + 1)/2) / n!`. -/
theorem repeatedGaussianIntegral_zero_right (n : ℕ) :
    repeatedGaussianIntegral n 0 =
      ((2 : ℝ) ^ (((n : ℝ) - 1) / 2) * Real.Gamma ((n + 1) / 2) / n ! : ℝ) := by
  have h := _root_.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := n) (b := 1 / 2)
    (by norm_num) (by have := n.cast_nonneg (α := ℝ); linarith) (by norm_num)
  have h2 : (2 : ℝ) ^ (((n : ℝ) - 1) / 2) = (1 / 2 : ℝ) ^ (-((n : ℝ) + 1) / 2) * (1 / 2) := by
    rw [one_div, Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two,
      ← Real.rpow_neg_one 2, ← Real.rpow_add zero_lt_two]
    congr 1
    ring
  rw [← Complex.ofReal_zero, repeatedGaussianIntegral_ofReal, h2, ← h, ← integral_div]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [Real.rpow_natCast, Real.rpow_two, zero_add,
    show -(t ^ 2) / 2 = -(1 / 2) * t ^ 2 by ring]
  ring

/-- `Hh₀(0) = √(π/2)`. -/
@[simp]
theorem repeatedGaussianIntegral_zero_zero : repeatedGaussianIntegral 0 0 = (√(π / 2) : ℝ) := by
  rw [repeatedGaussianIntegral_zero_right]
  congr 1
  rw [Nat.cast_zero, zero_sub, zero_add, Real.Gamma_one_half_eq, Nat.factorial_zero,
    Nat.cast_one, div_one, Real.sqrt_div' π zero_le_two, Real.sqrt_eq_rpow 2, neg_div,
    Real.rpow_neg zero_le_two, inv_mul_eq_div]

/-- Reality and positivity of `Hh_n(x)` for real `x`. -/
theorem repeatedGaussianIntegral_ofReal_pos (n : ℕ) (x : ℝ) :
    (repeatedGaussianIntegral n x).im = 0 ∧ 0 < (repeatedGaussianIntegral n x).re := by
  rw [repeatedGaussianIntegral_ofReal, Complex.ofReal_im, Complex.ofReal_re]
  refine ⟨rfl, ?_⟩
  have hpos : ∀ t ∈ Ioi (0 : ℝ), 0 < t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2) := fun t ht =>
    mul_pos (div_pos (pow_pos ht n) (mod_cast n.factorial_pos)) (Real.exp_pos _)
  have hint : IntegrableOn (fun t : ℝ => t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2)) (Ioi 0) := by
    refine ((repeatedGaussianIntegral_convergent n x).re).congr_fun (fun t _ => ?_)
      measurableSet_Ioi
    have hpt : (t : ℂ) ^ n / n ! * cexp (-((x + t) ^ 2) / 2) =
        ((t ^ n / n ! * Real.exp (-((x + t) ^ 2) / 2) : ℝ) : ℂ) := by
      push_cast
      rfl
    simp only [hpt, RCLike.re_to_complex, Complex.ofReal_re]
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hpos t ht).le) hint]
  refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi 0) fun t ht => ⟨(hpos t ht).ne', ht⟩)
  simp

/-- On the real line, `Hh₀(x) = √(π/2) erfc(x/√2)`. -/
theorem repeatedGaussianIntegral_zero_ofReal_eq_erfc (x : ℝ) :
    repeatedGaussianIntegral 0 x = ((√(π / 2) * TauCeti.Real.erfc (x / √2) : ℝ) : ℂ) := by
  have hs2 : (√2 : ℝ) ≠ 0 := by positivity
  have hsπ : (√π : ℝ) ≠ 0 := by positivity
  have hG : ∀ y : ℝ, HasDerivAt (fun y : ℝ => √(π / 2) * TauCeti.Real.erfc (y / √2))
      (-Real.exp (-y ^ 2 / 2)) y := fun y => by
    refine (((TauCeti.Real.hasDerivAt_erfc (y / √2)).comp y
      ((hasDerivAt_id y).div_const √2)).const_mul √(π / 2)).congr_deriv ?_
    rw [div_pow, Real.sq_sqrt zero_le_two, Real.sqrt_div' π zero_le_two]
    field_simp
    rw [Real.sq_sqrt zero_le_two]
  have hD : ∀ y : ℝ, HasDerivAt (fun y : ℝ =>
      repeatedGaussianIntegral 0 y - ((√(π / 2) * TauCeti.Real.erfc (y / √2) : ℝ) : ℂ)) 0 y :=
    fun y => by
    convert (hasDerivAt_repeatedGaussianIntegral_zero y).comp_ofReal.sub (hG y).ofReal_comp
      using 1
    push_cast
    ring
  have h := is_const_of_deriv_eq_zero (fun y => (hD y).differentiableAt) (fun y => (hD y).deriv)
    x 0
  rw [sub_eq_iff_eq_add] at h
  rw [h, Complex.ofReal_zero, repeatedGaussianIntegral_zero_zero, zero_div,
    TauCeti.Real.erfc_zero, mul_one, sub_self, zero_add]

end TauCeti
