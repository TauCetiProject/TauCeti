/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ConvexTable.OrientedLine

/-!
# Oriented lines of the unit circle: checks

Checks for `TauCeti.ConvexTable.orientedLine` on the unit circle `s ↦ exp(is)`, the convex table
`TauCeti.ConvexTable.circle 1` of perimeter `2π`:

* the state `(0, π/2)` is the horizontal line through the origin oriented towards `−1`:
  `e = −1` and `c = (−1) × 1 = 0`;
* the tangent lines `δ = 0` and `δ = π` at `γ(0)` meet the region only on its frontier, so they
  are not in the image of the phase cylinder;
* the reversed line `(1, 0) = −(−1, 0)`, the same point set, is the state `(π, π/2)`: it enters
  the disc at the exit point `γ(π) = −1` of `(0, π/2)`, with angle `π − π/2 = π/2`.
-/

public section

noncomputable section

open Set Complex TauCeti ConvexTable

namespace TauCeti.Examples.ConvexTableOrientedLine

/-- The unit circle has positive perimeter `2π`. -/
instance instFactPosTwoPiMulOne : Fact (0 < 2 * Real.pi * 1) := ⟨by positivity⟩

/-- On the unit circle the state `(0, π/2)` is the horizontal line through the origin oriented
towards `−1`. -/
theorem orientedLine_circle_zero : (circle 1).orientedLine 0 (Real.pi / 2) = (-1, 0) := by
  have hdir : ((circle 1).orientedLine 0 (Real.pi / 2)).1 = -1 := by
    refine Circle.ext ?_
    simp [deriv_circle, circleMap, Complex.exp_pi_div_two_mul_I]
  refine Prod.ext hdir ?_
  rw [orientedLine_snd, ← coe_orientedLine_fst, hdir, circle_apply]
  simp [circleMap]

/-- The tangent line at `γ(0)` (`δ = 0`) does not meet the interior of the disc. -/
example : orientedLineSet ((circle 1).orientedLine 0 0) ∩ interior (circle 1).region = ∅ :=
  orientedLineSet_orientedLine_inter_interior_eq_empty _ Real.sin_zero

/-- The tangent line at `γ(0)` with the opposite orientation (`δ = π`) does not meet it either. -/
example : orientedLineSet ((circle 1).orientedLine 0 Real.pi) ∩ interior (circle 1).region = ∅ :=
  orientedLineSet_orientedLine_inter_interior_eq_empty _ Real.sin_pi

/-- The state `(π, π/2)`, entering at `γ(π) = −1`, is the reversed line `(1, 0)`. -/
theorem orientedLine_circle_pi : (circle 1).orientedLine Real.pi (Real.pi / 2) = (1, 0) := by
  have hdir : ((circle 1).orientedLine Real.pi (Real.pi / 2)).1 = 1 := by
    refine Circle.ext ?_
    simp [deriv_circle, circleMap, Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
  refine Prod.ext hdir ?_
  rw [orientedLine_snd, ← coe_orientedLine_fst, hdir, circle_apply]
  simp [circleMap, Complex.exp_pi_mul_I]

/-- The states `(0, π/2)` and `(π, π/2)` have opposite oriented lines, with the same point set. -/
example : (circle 1).orientedLine Real.pi (Real.pi / 2) =
    -(circle 1).orientedLine 0 (Real.pi / 2) := by
  rw [orientedLine_circle_pi, orientedLine_circle_zero, Prod.neg_mk, neg_neg, neg_zero]

/-- The exit point of `(0, π/2)` is `γ(π) = −1`, the entry point of the reversed line. -/
example : (circle 1).exitParam 0 (Real.pi / 2) = Real.pi := by
  rw [exitParam_circle 1 0 ⟨by positivity, by linarith [Real.pi_pos]⟩]
  ring

end TauCeti.Examples.ConvexTableOrientedLine
