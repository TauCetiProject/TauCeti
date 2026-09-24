/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Trigonometric bounds for triangle angles

The sine of `π / x` is positive for real `x > 1`. For angles `α, β > 0` and `γ ≥ 0` with
`α + β + γ < π`, the quotient `(cos α cos β + cos γ) / (sin α sin β)` is greater than `1`; by the
second hyperbolic law of cosines it is the hyperbolic cosine of the side opposite `γ` in a
hyperbolic triangle with angles `α`, `β`, `γ`. These supply the positive sine factors and the
hyperbolic scale in the matrix representations of triangle groups.
-/

public section

open Real

namespace TauCeti

/-- For a real denominator greater than one, the sine of `π / x` is positive. -/
theorem sin_pi_div_pos {x : ℝ} (hx : 1 < x) : 0 < sin (π / x) :=
  sin_pos_of_pos_of_lt_pi (div_pos pi_pos (by linarith)) (div_lt_self pi_pos hx)

/-- If `α, β > 0`, `γ ≥ 0` and `α + β + γ < π`, then `(cos α cos β + cos γ) / (sin α sin β) > 1`.
Indeed `cos α cos β - sin α sin β = -cos (π - α - β)`, and `cos (π - α - β) < cos γ` because
`0 ≤ γ < π - α - β ≤ π`. -/
theorem one_lt_cos_mul_cos_add_cos_div_sin_mul_sin {α β γ : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hγ : 0 ≤ γ) (h : α + β + γ < π) : 1 < (cos α * cos β + cos γ) / (sin α * sin β) := by
  have hs : 0 < sin α * sin β :=
    mul_pos (sin_pos_of_pos_of_lt_pi hα (by linarith)) (sin_pos_of_pos_of_lt_pi hβ (by linarith))
  have hcos : cos (π - (α + β)) < cos γ :=
    cos_lt_cos_of_nonneg_of_le_pi hγ (by linarith) (by linarith)
  rw [cos_pi_sub, cos_add] at hcos
  rw [one_lt_div hs]
  linarith

end TauCeti
