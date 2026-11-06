/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Shifting the argument of a decaying real exponential

The decay profile `exp (-c (t - R))`, normalised to equal `1` at `t = R`, is the radial profile
`exp (-c t)` rescaled by the constant amplitude `exp (c R)`. This is how exponential decay
estimates past a radius `R` are converted into bounds of the form `K exp (-c t)`.

## Main declarations

* `TauCeti.exp_neg_mul_sub`: `exp (-c (t - R)) = exp (c R) exp (-c t)`.
* `TauCeti.exists_le_mul_exp_of_continuousOn_closedBall`: a bound `f x ≤ K exp (-c ‖x‖)` for
  `‖x‖ ≥ R` extends to all `x`, with a larger constant, when `f` is continuous on the ball.
-/

public section

namespace TauCeti

/-- Shifting the radius in an exponential: `exp (-c (t - R)) = exp (c R) exp (-c t)`. -/
theorem exp_neg_mul_sub (c t R : ℝ) :
    Real.exp (-(c * (t - R))) = Real.exp (c * R) * Real.exp (-(c * t)) := by
  rw [← Real.exp_add]
  ring_nf

/-- An exponential bound `f x ≤ K exp (-c ‖x‖)` outside a ball extends to the whole space, with a
nonnegative constant, when `f` is continuous on the closed ball: there `f` is bounded, and
`exp (-c ‖x‖)` is bounded below by `exp (-|c| R)`. -/
theorem exists_le_mul_exp_of_continuousOn_closedBall {E : Type*} [SeminormedAddCommGroup E]
    [ProperSpace E] {f : E → ℝ} {R K c : ℝ} (hf : ContinuousOn f (Metric.closedBall 0 R))
    (hK : ∀ x, R ≤ ‖x‖ → f x ≤ K * Real.exp (-(c * ‖x‖))) :
    ∃ K', 0 ≤ K' ∧ ∀ x, f x ≤ K' * Real.exp (-(c * ‖x‖)) := by
  obtain ⟨B, hB⟩ := (isCompact_closedBall (0 : E) R).exists_bound_of_continuousOn hf
  refine ⟨max K (max B 0 * Real.exp (|c| * R)),
    (by positivity : 0 ≤ max B 0 * Real.exp (|c| * R)).trans (le_max_right _ _), fun x ↦ ?_⟩
  rcases le_or_gt R ‖x‖ with hx | hx
  · exact (hK x hx).trans (by gcongr; exact le_max_left _ _)
  · have hfx : f x ≤ max B 0 := ((le_abs_self _).trans (by simpa using hB x (by
      simpa using hx.le))).trans (le_max_left _ _)
    have hone : 1 ≤ Real.exp (|c| * R) * Real.exp (-(c * ‖x‖)) := by
      rw [← Real.exp_add]
      refine Real.one_le_exp ?_
      linarith [mul_le_mul_of_nonneg_left hx.le (abs_nonneg c),
        mul_le_mul_of_nonneg_right (le_abs_self c) (norm_nonneg x)]
    calc f x ≤ max B 0 * (Real.exp (|c| * R) * Real.exp (-(c * ‖x‖))) :=
          hfx.trans (le_mul_of_one_le_right (le_max_right _ _) hone)
      _ = max B 0 * Real.exp (|c| * R) * Real.exp (-(c * ‖x‖)) := by ring
      _ ≤ _ := by gcongr; exact le_max_right _ _

end TauCeti
