/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Basic facts about circular parametrizations

The derivative of `circleMap c R` is continuous (`Complex.continuous_deriv_circleMap`).

The trace of a circular parametrization over `[0,2π]` is the sphere, for arbitrary signed radii.
Consequently the exponential `t ↦ exp (2π i t / L)` and its conjugate cover the unit circle over
`[0, L]` (`Complex.image_exp_two_pi_I_div_Icc`, `Complex.image_exp_neg_two_pi_I_div_Icc`).

Substituting `w = 1/z` in a circle integral reverses the orientation of the circle:
`∮_{|w| = r} -g(1/w)/w² dw = -∮_{|z| = 1/r} g(z) dz`
(`TauCeti.Contour.circleIntegral_neg_inv_sq_smul_comp_inv`).
-/

public section

open Set Metric
open scoped Real

namespace Complex

/-- The derivative of the circle parametrisation `circleMap c R` is continuous. -/
theorem continuous_deriv_circleMap (c : ℂ) (R : ℝ) : Continuous (deriv (circleMap c R)) := by
  rw [funext (deriv_circleMap c R)]
  fun_prop

/-- The full circular trace over `[0,2π]` is exactly the circle. -/
theorem image_circleMap_uIcc (c : ℂ) (R : ℝ) :
    circleMap c R '' uIcc 0 (2 * Real.pi) = sphere c |R| := by
  rw [uIcc_of_le Real.two_pi_pos.le]
  simpa only [zero_add, range_circleMap] using
    (periodic_circleMap c R).image_Icc (a := 0) Real.two_pi_pos

/-- One turn of a unit circular exponential, rescaled to the interval `[0, L]` of positive length
`L`, covers the unit circle, including both endpoints. -/
theorem image_exp_two_pi_I_div_Icc {L : ℝ} (hL : 0 < L) :
    (fun t : ℝ ↦ exp (2 * π * I * t / L)) '' Icc 0 L = sphere (0 : ℂ) 1 := by
  -- Rescaling a full length interval gives a full angular period, including both endpoints.
  have hangle : (fun t : ℝ ↦ 2 * π * t / L) '' Icc 0 L = uIcc 0 (2 * π) := by
    rw [← uIcc_of_le hL.le]
    have hscale : (fun t : ℝ ↦ 2 * π * t / L) = fun t ↦ t * (2 * π / L) := by
      funext t
      ring
    rw [hscale, image_mul_const_uIcc]
    congr 1
    · simp
    · field_simp
  calc
    _ = circleMap 0 1 '' ((fun t : ℝ ↦ 2 * π * t / L) '' Icc 0 L) := by
      rw [image_image]
      congr 1
      funext t
      simp only [circleMap, ofReal_one, one_mul, zero_add, ofReal_div, ofReal_mul,
        ofReal_ofNat]
      congr 1
      ring
    _ = sphere (0 : ℂ) 1 := by rw [hangle, image_circleMap_uIcc]; simp

/-- The conjugate circular exponential `t ↦ exp (-(2π i t / L))` also covers the unit circle over
`[0, L]`. -/
theorem image_exp_neg_two_pi_I_div_Icc {L : ℝ} (hL : 0 < L) :
    (fun t : ℝ ↦ exp (-(2 * π * I * t / L))) '' Icc 0 L = sphere (0 : ℂ) 1 := by
  calc
    _ = conjLIE '' ((fun t : ℝ ↦ exp (2 * π * I * t / L)) '' Icc 0 L) := by
      rw [image_image]
      congr 1
      funext t
      simp [conjLIE_apply, ← exp_conj, map_ofNat, neg_div]
    _ = sphere (0 : ℂ) 1 := by
      rw [image_exp_two_pi_I_div_Icc hL, conjLIE.image_sphere]
      simp

end Complex

namespace TauCeti.Contour

open Complex Function

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Inversion of a circle integral.** Substituting `w = 1/z` turns the circle `|w| = r` into the
circle `|z| = 1/r` traversed in the opposite direction, and `dw = -dz / z²`. So if
`h(w) = -g(1/w) / w²`, then `∮_{|w| = r} h(w) dw = -∮_{|z| = 1/r} g(z) dz`. -/
theorem circleIntegral_neg_inv_sq_smul_comp_inv (g : ℂ → E) (r : ℝ) :
    (∮ w in C(0, r), (-(w ^ 2)⁻¹) • g w⁻¹) = -∮ z in C(0, r⁻¹), g z := by
  set F : ℝ → E := fun θ ↦ (circleMap 0 r⁻¹ θ * I) • g (circleMap 0 r⁻¹ θ) with hF
  have hpt : ∀ θ : ℝ, (circleMap 0 r θ * I) • ((-(circleMap 0 r θ ^ 2)⁻¹) •
      g (circleMap 0 r θ)⁻¹) = -F (-θ) := by
    intro θ
    simp only [hF]
    rw [← circleMap_zero_inv, smul_smul, ← neg_smul]
    congr 1
    rcases eq_or_ne (circleMap 0 r θ) 0 with h | h
    · simp [h]
    · field_simp
  have hper : Periodic F (2 * π) := fun θ ↦ by
    simp only [hF, periodic_circleMap 0 r⁻¹ θ]
  simp only [circleIntegral, deriv_circleMap, hpt, intervalIntegral.integral_neg,
    intervalIntegral.integral_comp_neg, neg_zero]
  congr 1
  simpa using hper.intervalIntegral_add_eq (-(2 * π)) 0

end TauCeti.Contour
