/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Circle integrals of a simple principal part

The principal part `z ↦ A · (z − s)⁻¹` is circle integrable on `C(c, R)`, with integral `2πi A`,
whenever it is not a genuine pole on or outside the circle: either `A = 0` or `s` lies strictly
inside the circle. Stating the hypothesis as this disjunction lets sums of principal parts be
integrated termwise without case splits on vanishing coefficients.

The interior case is Mathlib's `circleIntegral.integral_sub_inv_of_mem_ball`.

## Main results

* `TauCeti.Contour.circleIntegrable_const_mul_sub_inv` — circle integrability of `A · (z − s)⁻¹`.
* `TauCeti.Contour.circleIntegral_const_mul_sub_inv` — its integral over `C(c, R)` is `2πi A`.
-/

public section

noncomputable section

open Metric

namespace TauCeti.Contour

/-- A principal part `A / (z - s)` is circle integrable on `C(c, R)` if it vanishes or `s` lies
strictly inside the circle. -/
theorem circleIntegrable_const_mul_sub_inv {A c s : ℂ} {R : ℝ}
    (hs : A = 0 ∨ s ∈ ball c R) : CircleIntegrable (fun z => A * (z - s)⁻¹) c R := by
  rcases hs with rfl | hs
  · simp
  refine (circleIntegrable_sub_inv_iff.2 (Or.inr fun hsp => ?_)).const_fun_smul (a := A)
  rw [abs_of_pos (pos_of_mem_ball hs)] at hsp
  exact (mem_ball.1 hs).ne (mem_sphere.1 hsp)

/-- The integral of a principal part `A / (z - s)` over `C(c, R)` is `2πi A` if it vanishes or `s`
lies strictly inside the circle. -/
theorem circleIntegral_const_mul_sub_inv {A c s : ℂ} {R : ℝ}
    (hs : A = 0 ∨ s ∈ ball c R) :
    circleIntegral (fun z => A * (z - s)⁻¹) c R = 2 * (Real.pi : ℂ) * Complex.I * A := by
  rw [circleIntegral.integral_const_mul]
  rcases hs with rfl | hs
  · simp
  rw [circleIntegral.integral_sub_inv_of_mem_ball hs, mul_comm]

end TauCeti.Contour

end
