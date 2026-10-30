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

The principal part `z ↦ A · (z − s)⁻¹` is circle integrable on `C(c, R)` unless it has a genuine
pole on a nondegenerate circle: it suffices that `A = 0`, `R = 0`, or `s ∉ sphere c |R|`. Its
integral is `2πi A` whenever `A = 0` or `s` lies strictly inside the circle. Stating the
hypotheses as disjunctions lets sums of principal parts be integrated termwise without case splits
on vanishing coefficients.

The integrability statement reduces to Mathlib's `circleIntegrable_sub_inv_iff`, and the interior
integral is Mathlib's `circleIntegral.integral_sub_inv_of_mem_ball`.

## Main results

* `TauCeti.Contour.circleIntegrable_const_mul_sub_inv` — circle integrability of `A · (z − s)⁻¹`.
* `TauCeti.Contour.circleIntegral_const_mul_sub_inv` — its integral over `C(c, R)` is `2πi A`.
-/

public section

noncomputable section

open Metric

namespace TauCeti.Contour

/-- A principal part `A / (z - s)` is circle integrable on `C(c, R)` if it vanishes, the circle
is degenerate, or `s` does not lie on the circle. -/
theorem circleIntegrable_const_mul_sub_inv {A c s : ℂ} {R : ℝ}
    (hs : A = 0 ∨ R = 0 ∨ s ∉ sphere c |R|) : CircleIntegrable (fun z => A * (z - s)⁻¹) c R := by
  rcases hs with rfl | hs
  · simp
  exact (circleIntegrable_sub_inv_iff.2 hs).const_fun_smul (a := A)

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
