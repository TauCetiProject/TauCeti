/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.LaplaceTransform

/-!
# Gaussian transforms over a compact interval

For `g : ℝ → ℂ` and `c : ℂ`, this file studies the Gaussian transform
`z ↦ ∫ y in a..b, g y * exp (-c (z - y)²)` of `g` over a compact interval `[a, b]`.
Expanding the square identifies it with `exp (-c z²)` times a truncated Laplace transform, so it
is entire. For real `c ≥ 0` and bounded `g`, it decays like a Gaussian in the distance from
`re z` to `[a, b]`, uniformly on horizontal strips.

On `ℝ`, heat kernel smoothings of functions supported in `[a, b]` are Gaussian transforms of this
form (`TauCeti.heatKernel_convolution_eq_intervalIntegral`), so these results extend them to
entire functions with explicit bounds.

## Main declarations

* `TauCeti.differentiable_intervalIntegral_mul_cexp_neg_mul_sub_sq`: Gaussian transforms over a
  compact interval are entire.
* `TauCeti.norm_intervalIntegral_mul_cexp_neg_mul_sub_sq_le`: their Gaussian bound in terms of
  the distance from `re z` to `[a, b]` and of `im z`.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti

/-- **Gaussian transforms over a compact interval are entire.** For `g` integrable on `[a, b]`,
the function `z ↦ ∫ y in a..b, g y * exp (-c (z - y)²)` is complex differentiable everywhere. -/
theorem differentiable_intervalIntegral_mul_cexp_neg_mul_sub_sq {g : ℝ → ℂ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (c : ℂ) :
    Differentiable ℂ fun z : ℂ ↦ ∫ y in a..b, g y * cexp (-c * (z - y) ^ 2) := by
  -- Expanding the square writes the transform as `exp (-c z²)` times a truncated Laplace
  -- transform evaluated at `-2 c z`.
  have hL := differentiable_intervalIntegral_mul_cexp_neg_mul
    (hg.mul_continuousOn
      (by fun_prop : Continuous fun y : ℝ ↦ cexp (-c * (y : ℂ) ^ 2)).continuousOn)
  have key : (fun z : ℂ ↦ ∫ y in a..b, g y * cexp (-c * (z - y) ^ 2)) =
      fun z ↦ cexp (-c * z ^ 2) *
        ∫ y in a..b, (g y * cexp (-c * (y : ℂ) ^ 2)) * cexp (-(-2 * c * z) * y) := by
    funext z
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext y
    rw [mul_comm (cexp _), mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    ring_nf
  rw [key]
  exact (by fun_prop : Differentiable ℂ fun z : ℂ ↦ cexp (-c * z ^ 2)).mul
    (hL.comp (by fun_prop))

/-- **Gaussian bound for Gaussian transforms.** If `‖g‖ ≤ M` on `[a, b]`, `c ≥ 0`, and `re z` has
distance at least `D ≥ 0` from every point of `[a, b]`, then
`‖∫ y in a..b, g y * exp (-c (z - y)²)‖ ≤ M exp (-c (D² - (im z)²)) (b - a)`. -/
theorem norm_intervalIntegral_mul_cexp_neg_mul_sub_sq_le {g : ℝ → ℂ} {a b c M D : ℝ}
    (hab : a ≤ b) (hc : 0 ≤ c) (hD : 0 ≤ D) (hM : ∀ y ∈ Icc a b, ‖g y‖ ≤ M) {z : ℂ}
    (hz : ∀ y ∈ Icc a b, D ≤ |z.re - y|) :
    ‖∫ y in a..b, g y * cexp (-c * (z - y) ^ 2)‖ ≤
      M * Real.exp (-c * (D ^ 2 - z.im ^ 2)) * (b - a) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
    (f := fun y : ℝ ↦ g y * cexp (-c * (z - y) ^ 2))
    (C := M * Real.exp (-c * (D ^ 2 - z.im ^ 2))) ?_
  · rwa [abs_of_nonneg (sub_nonneg.2 hab)] at this
  intro y hy
  have hy' : y ∈ Icc a b := Ioc_subset_Icc_self (by rwa [uIoc_of_le hab] at hy)
  have hre : (-(c : ℂ) * (z - y) ^ 2).re = -c * ((z.re - y) ^ 2 - z.im ^ 2) := by
    simp [sq, Complex.mul_re, Complex.sub_re, Complex.sub_im]
  rw [norm_mul, Complex.norm_exp, hre]
  refine mul_le_mul (hM y hy') (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    ((norm_nonneg _).trans (hM y hy'))
  have : D ^ 2 ≤ (z.re - y) ^ 2 := by
    rw [← sq_abs (z.re - y)]
    exact pow_le_pow_left₀ hD (hz y hy') 2
  nlinarith

end TauCeti
