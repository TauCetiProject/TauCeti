/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Newman.Transform

/-!
# The semicircle contributions in Newman's argument

The right semicircle is parametrized counterclockwise from `-R * I` to `R * I` by
`circleMap 0 R` on `[-π/2, π/2]`. The left semicircle continues counterclockwise back to
`-R * I` on `[π/2, 3π/2]`. All integrals below include the velocity `z * I` of this
parametrization.

For a bounded function on the positive half-line, the right semicircle contribution of the
Laplace-transform tail and the left semicircle contribution of the truncated transform each
have norm at most `M / R` after division by `2πi`. Continuity of the continuation on the
closed right arc gives integrability at the imaginary endpoints; the kernel's polynomial
factor vanishes there. No estimate divides by the real part at an endpoint.

The final identity splits Cauchy's formula for the truncated transform into these two oriented
semicircles. Together these results isolate the circular contributions from the separate
left-detour contribution for a holomorphic continuation.

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

variable {f : ℝ → ℂ} {G : ℂ → ℂ} {M T R : ℝ}

private theorem continuousOn_semicircle_integrand {w : ℂ → ℂ} {a b : ℝ}
    (hR : 0 < R) (hw : ContinuousOn w (circleMap 0 R '' uIcc a b)) :
    ContinuousOn (fun θ : ℝ ↦ circleMap 0 R θ * Complex.I *
      (w (circleMap 0 R θ) * cexp (T * circleMap 0 R θ) *
        (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) / circleMap 0 R θ)) (uIcc a b) := by
  have hc := hw.comp (continuous_circleMap 0 R).continuousOn (mapsTo_image _ _)
  exact ((continuous_circleMap 0 R).continuousOn.mul continuousOn_const).mul
    (((hc.mul (by fun_prop)).mul (by fun_prop)).div
      (continuous_circleMap 0 R).continuousOn (fun θ _ ↦ circleMap_ne_center hR.ne'))

private theorem mul_kernel_eq_zero_of_re_eq_zero {w z : ℂ}
    (hR : 0 < R) (hz : ‖z‖ = R) (hre : z.re = 0) :
    w * cexp (T * z) * (1 + z ^ 2 / (R : ℂ) ^ 2) / z = 0 := by
  have hp : 1 + z ^ 2 / (R : ℂ) ^ 2 = 0 := by
    apply norm_eq_zero.mp
    rw [Complex.norm_one_add_sq_div_sq_of_norm_eq hz hR, hre, abs_zero, mul_zero, zero_div]
  simp [hp]

private theorem norm_integral_semicircle_mul_kernel_le {w : ℂ → ℂ} {a b : ℝ}
    (hM : 0 ≤ M) (hR : 0 < R) (hlength : b - a = π)
    (hw : ∀ θ ∈ Ioc a b, (circleMap 0 R θ).re ≠ 0 →
      ‖w (circleMap 0 R θ) * cexp (T * circleMap 0 R θ) *
        (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) / circleMap 0 R θ‖ ≤ 2 * M / R ^ 2) :
    ‖(∫ θ in a..b, circleMap 0 R θ * Complex.I *
      (w (circleMap 0 R θ) * cexp (T * circleMap 0 R θ) *
        (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) / circleMap 0 R θ)) /
          (2 * π * Complex.I)‖ ≤ M / R := by
  have hi : ‖∫ θ in a..b, circleMap 0 R θ * Complex.I *
      (w (circleMap 0 R θ) * cexp (T * circleMap 0 R θ) *
        (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) / circleMap 0 R θ)‖ ≤
        (R * (2 * M / R ^ 2)) * π := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const
      (C := R * (2 * M / R ^ 2)) ?_).trans_eq ?_
    · intro θ hθ
      rw [uIoc_of_le (by linarith [Real.pi_pos] : a ≤ b)] at hθ
      have hz : ‖circleMap 0 R θ‖ = R := by simp [abs_of_pos hR]
      by_cases hzero : (circleMap 0 R θ).re = 0
      · rw [mul_kernel_eq_zero_of_re_eq_zero hR hz hzero, mul_zero, norm_zero]
        positivity
      · rw [norm_mul, norm_mul, hz, Complex.norm_I, mul_one]
        exact mul_le_mul_of_nonneg_left (hw θ hθ hzero) hR.le
    · rw [hlength, abs_of_pos Real.pi_pos]
  rw [norm_div, norm_mul, norm_mul]
  simp only [Complex.norm_I, mul_one, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  calc _ ≤ R * (2 * M / R ^ 2) * π / (2 * π) := by gcongr
       _ = M / R := by field_simp

/-- The right-arc tail integrand is integrable, including both imaginary endpoints, whenever
the continuation is continuous on that closed arc. -/
theorem intervalIntegrable_right_semicircle_mul_kernel
    (hf : IntervalIntegrable f volume 0 T) (hR : 0 < R)
    (hG : ContinuousOn G (circleMap 0 R '' Icc (-π / 2) (π / 2))) :
    IntervalIntegrable (fun θ : ℝ ↦ circleMap 0 R θ * Complex.I *
      ((G (circleMap 0 R θ) - ∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
        cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
          circleMap 0 R θ)) volume (-π / 2) (π / 2) := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_semicircle_integrand (w := fun z ↦
    G z - ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) hR
  rw [uIcc_of_le (by linarith [Real.pi_pos] : -π / 2 ≤ π / 2)]
  exact hG.sub (differentiable_intervalIntegral_mul_cexp_neg_mul hf).continuous.continuousOn

/-- The truncated-transform kernel integrand along a circle is integrable on every finite
angle interval, including the imaginary endpoints of either semicircle. -/
theorem intervalIntegrable_circleMap_intervalIntegral_mul_kernel {a b : ℝ}
    (hf : IntervalIntegrable f volume 0 T) (hR : 0 < R) :
    IntervalIntegrable (fun θ : ℝ ↦ circleMap 0 R θ * Complex.I *
      ((∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
        cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
          circleMap 0 R θ)) volume a b := by
  exact ContinuousOn.intervalIntegrable <| continuousOn_semicircle_integrand hR
    (differentiable_intervalIntegral_mul_cexp_neg_mul hf).continuous.continuousOn

/-- The normalized right semicircle integral of the Laplace-transform tail has norm at most
`M / R`. The contour runs from `-R * I` to `R * I` through the right half-plane.
Only agreement with the Laplace transform in the open right half-plane is needed for the bound;
`intervalIntegrable_right_semicircle_mul_kernel` supplies integrability from continuity. -/
theorem norm_integral_right_semicircle_mul_kernel_le
    (hf : AEStronglyMeasurable f (volume.restrict (Ici 0)))
    (hbound : ∀ t ∈ Ici (0 : ℝ), ‖f t‖ ≤ M)
    (hG : ∀ z : ℂ, 0 < z.re → G z = ∫ t in Ici (0 : ℝ), f t * cexp (-z * t))
    (hR : 0 < R) (hT : 0 ≤ T) :
    ‖(∫ θ in (-π / 2)..(π / 2), circleMap 0 R θ * Complex.I *
      ((G (circleMap 0 R θ) - ∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
        cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
          circleMap 0 R θ)) / (2 * π * Complex.I)‖ ≤ M / R := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hbound 0 (by simp))
  apply norm_integral_semicircle_mul_kernel_le
    (w := fun z ↦ G z - ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) hM hR (by ring)
  intro θ hθ hzero
  have hz : ‖circleMap 0 R θ‖ = R := by simp [abs_of_pos hR]
  have hre : 0 ≤ (circleMap 0 R θ).re := by
    rw [circleMap_zero_re]
    exact mul_nonneg hR.le (Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1], hθ.2⟩)
  rw [hG _ (lt_of_le_of_ne hre (Ne.symm hzero))]
  exact norm_integral_sub_intervalIntegral_mul_kernel_le hf hbound hz hR
    (lt_of_le_of_ne hre (Ne.symm hzero)) hT

/-- The normalized left semicircle integral of the truncated transform has norm at most
`M / R`. The contour runs from `R * I` to `-R * I` through the left half-plane. -/
theorem norm_integral_left_semicircle_mul_kernel_le
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ‖f t‖ ≤ M) (hR : 0 < R) (hT : 0 ≤ T) :
    ‖(∫ θ in (π / 2)..(3 * π / 2), circleMap 0 R θ * Complex.I *
      ((∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
        cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
          circleMap 0 R θ)) / (2 * π * Complex.I)‖ ≤ M / R := by
  have hM : 0 ≤ M := (norm_nonneg (f 0)).trans (hbound 0 ⟨le_rfl, hT⟩)
  apply norm_integral_semicircle_mul_kernel_le
    (w := fun z ↦ ∫ t in (0 : ℝ)..T, f t * cexp (-z * t)) hM hR (by ring)
  intro θ hθ hzero
  have hz : ‖circleMap 0 R θ‖ = R := by simp [abs_of_pos hR]
  have hre : (circleMap 0 R θ).re ≤ 0 := by
    rw [circleMap_zero_re]
    exact mul_nonpos_of_nonneg_of_nonpos hR.le
      (Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith [hθ.1]) (by linarith [hθ.2]))
  exact norm_intervalIntegral_mul_kernel_le_of_re_neg hbound hz hR
    (lt_of_le_of_ne hre hzero) hT

/-- Cauchy's formula for the truncated transform, split into the counterclockwise right
and left semicircles and normalized by `2πi`. Both arcs are traversed in increasing angle. -/
theorem integral_semicircles_intervalIntegral_mul_kernel
    (hf : IntervalIntegrable f volume 0 T) (hR : 0 < R) :
    ((∫ θ in (-π / 2)..(π / 2), circleMap 0 R θ * Complex.I *
        ((∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
          cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
            circleMap 0 R θ)) +
      ∫ θ in (π / 2)..(3 * π / 2), circleMap 0 R θ * Complex.I *
        ((∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
          cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
            circleMap 0 R θ)) / (2 * π * Complex.I) = ∫ t in (0 : ℝ)..T, f t := by
  let H : ℝ → ℂ := fun θ ↦ circleMap 0 R θ * Complex.I *
    ((∫ t in (0 : ℝ)..T, f t * cexp (-circleMap 0 R θ * t)) *
      cexp (T * circleMap 0 R θ) * (1 + circleMap 0 R θ ^ 2 / (R : ℂ) ^ 2) /
        circleMap 0 R θ)
  have hI (a b : ℝ) : IntervalIntegrable H volume a b :=
    intervalIntegrable_circleMap_intervalIntegral_mul_kernel hf hR
  have hp : Function.Periodic H (2 * π) := by
    intro θ
    simp only [H, (periodic_circleMap 0 R) θ]
  have he : (∫ θ in (0 : ℝ)..(2 * π), H θ) =
      ∫ θ in (-π / 2)..(3 * π / 2), H θ := by
    convert hp.intervalIntegral_add_eq 0 (-π / 2) using 1 <;> congr 1 <;> ring
  have hc : (∫ θ in (0 : ℝ)..(2 * π), H θ) =
      2 * π * Complex.I * ∫ t in (0 : ℝ)..T, f t := by
    simpa only [circleIntegral, deriv_circleMap, smul_eq_mul] using
      circleIntegral_intervalIntegral_mul_kernel hf hR
  rw [intervalIntegral.integral_add_adjacent_intervals (hI _ _) (hI _ _), ← he, hc]
  exact mul_div_cancel_left₀ _ (by simp [Real.pi_ne_zero])

end TauCeti.LSeries
