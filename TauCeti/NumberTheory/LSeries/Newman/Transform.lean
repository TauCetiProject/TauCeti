/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import TauCeti.Analysis.Complex.LaplaceTransform
public import TauCeti.Analysis.Complex.NormSq

/-!
# Truncated Laplace transforms and the estimates of Newman's contour argument

Let `f : ℝ → ℂ` be bounded by `M` on `[0, ∞)`. Newman's Tauberian theorem compares the
Laplace transform `G z = ∫ t in Ici 0, f t * exp (-z t)` with its truncations
`G_T z = ∫ t in 0..T, f t * exp (-z t)` against the kernel `exp (T z) (1 + z² / R²) / z` on
the circle `‖z‖ = R`. Combining the general Laplace estimates of
`TauCeti.Analysis.Complex.LaplaceTransform` (truncations are entire, the transform is holomorphic
on `0 < re z`, and the tail and left half-plane bounds) with the identity
`‖1 + z² / R²‖ = 2 |re z| / R` on the circle `‖z‖ = R`, this file proves:

* the kernel cancellation `norm_mul_kernel_le_of_norm_eq`: on the circle, if
  `‖w‖ ≤ M exp (-T re z) / |re z|` then `w` times the kernel has norm at most `2 M / R²`;
* consequently, both integrands of the contour argument are bounded by `2 M / R²`, uniformly in
  `T`;
* Cauchy's formula for the entire function `G_T`: its kernel integral over the full circle
  is `2πi ∫ t in 0..T, f t`.

The factor `exp (T z)` cancels the decay `exp (-T re z)`, making the bounds independent of `T`;
the factor `1 + z² / R²` cancels the small denominator `re z` on the circle, making them uniform
up to the imaginary axis.

## References

* D. J. Newman, *Simple analytic proof of the prime number theorem*, Amer. Math. Monthly 87
  (1980), 693–696.
* D. Zagier, *Newman's short proof of the prime number theorem*, Amer. Math. Monthly 104
  (1997), 705–708.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology Real Complex Interval

namespace TauCeti.LSeries

variable {f : ℝ → ℂ} {M T : ℝ}

/-- **Kernel cancellation.** On the circle `‖z‖ = R` off the imaginary axis, if `‖w‖` is at most
`M exp (-T re z) / |re z|`, then `w` multiplied by Newman's kernel `exp (T z) (1 + z² / R²) / z`
has norm at most `2 M / R²`: the factor `exp (T z)` cancels `exp (-T re z)` and the factor
`1 + z² / R²` cancels the denominator `|re z|`. -/
theorem norm_mul_kernel_le_of_norm_eq {w z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hR : 0 < R)
    (hre : z.re ≠ 0) (hw : ‖w‖ ≤ M * Real.exp (-z.re * T) / |z.re|) :
    ‖w * cexp (T * z) * (1 + z ^ 2 / (R : ℂ) ^ 2) / z‖ ≤ 2 * M / R ^ 2 := by
  rw [norm_div, norm_mul, norm_mul, Complex.norm_exp, Complex.re_ofReal_mul,
    Complex.norm_one_add_sq_div_sq_of_norm_eq hz hR, hz]
  calc _ ≤ M * Real.exp (-z.re * T) / |z.re| * Real.exp (T * z.re) * (2 * |z.re| / R) / R := by
        gcongr
    _ = 2 * M / R ^ 2 := by
        have he : Real.exp (T * z.re) = (Real.exp (-z.re * T))⁻¹ := by
          rw [← Real.exp_neg]; ring_nf
        have hre0 : |z.re| ≠ 0 := abs_ne_zero.mpr hre
        rw [he]
        field_simp

/-- **Right-arc integrand bound.** On the circle `‖z‖ = R` with `0 < re z`, the difference
between the Laplace transform of a function bounded by `M` on `[0, ∞)` and its truncation at
`T ≥ 0`, multiplied by Newman's kernel `exp (T z) (1 + z² / R²) / z`, is at most `2 M / R²`. -/
theorem norm_integral_sub_intervalIntegral_mul_kernel_le
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M) {z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hR : 0 < R)
    (hre : 0 < z.re) (hT : 0 ≤ T) :
    ‖((∫ t in Ici (0 : ℝ), f t * cexp (-z * t)) - ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) *
        cexp (T * z) * (1 + z ^ 2 / (R : ℂ) ^ 2) / z‖ ≤ 2 * M / R ^ 2 :=
  norm_mul_kernel_le_of_norm_eq hz hR hre.ne' <| by
    simpa only [abs_of_pos hre] using
      norm_integral_sub_intervalIntegral_mul_cexp_neg_mul_le hf hbound hre hT

/-- **Left-arc integrand bound.** On the circle `‖z‖ = R` with `re z < 0`, the truncation at
`T ≥ 0` of the Laplace transform of a function bounded by `M` on `[0, T]`, multiplied by
Newman's kernel `exp (T z) (1 + z² / R²) / z`, is at most `2 M / R²`. -/
theorem norm_intervalIntegral_mul_kernel_le_of_re_neg
    (hbound : ∀ t ∈ Icc 0 T, ‖f t‖ ≤ M) {z : ℂ} {R : ℝ} (hz : ‖z‖ = R) (hR : 0 < R)
    (hre : z.re < 0) (hT : 0 ≤ T) :
    ‖(∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) * cexp (T * z) * (1 + z ^ 2 / (R : ℂ) ^ 2) / z‖ ≤
      2 * M / R ^ 2 :=
  norm_mul_kernel_le_of_norm_eq hz hR hre.ne <| by
    simpa only [abs_of_neg hre] using
      norm_intervalIntegral_mul_cexp_neg_mul_le_of_re_neg hbound hre hT

/-- **Cauchy's formula for a truncated transform.** For `R > 0`, the integral of the truncated
Laplace transform against Newman's kernel `exp (T z) (1 + z² / R²) / z` over the circle
`‖z‖ = R` is `2πi` times its value at `0`, namely `2πi ∫ t in 0..T, f t`. -/
theorem circleIntegral_intervalIntegral_mul_kernel (hf : IntervalIntegrable f volume 0 T)
    {R : ℝ} (hR : 0 < R) :
    (∮ z in C(0, R), (∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) * cexp (T * z) *
        (1 + z ^ 2 / (R : ℂ) ^ 2) / z) = 2 * π * Complex.I * ∫ t in (0 : ℝ)..T, f t := by
  have hd : Differentiable ℂ fun z : ℂ ↦
      (∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) * cexp (T * z) * (1 + z ^ 2 / (R : ℂ) ^ 2) :=
    ((differentiable_intervalIntegral_mul_cexp_neg_mul hf).mul (by fun_prop)).mul (by fun_prop)
  have h := hd.differentiableOn.circleIntegral_sub_inv_smul (c := 0) (R := R)
    (w := 0) (mem_ball_self hR)
  simp only [sub_zero, smul_eq_mul, neg_zero, zero_mul, Complex.exp_zero, mul_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, add_zero, mul_zero] at h
  simpa only [inv_mul_eq_div, mul_comm] using h

end TauCeti.LSeries
