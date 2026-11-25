/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Circle
public import TauCeti.Dynamics.Billiard.OrientedLine

/-!
# Oriented-line coordinates on the circular table: checks

Checks for `TauCeti.StrictConvexBilliardTable.orientedLine` on the circular table of radius `R`
about the origin of `ℂ` (`TauCeti.StrictConvexBilliardTable.circle`), with `χ(0) = R`.

* The state `(0, 0)`, leaving `χ(0) = R` along the inward normal, has the horizontal line through
  the origin oriented towards `-1`: `Λ(0, 0) = (-1, 0)`.
* The reversed state at its next collision point `χ(π R) = -R` has the same line with the reverse
  orientation, `(1, 0)`.
-/

public section

noncomputable section

open Complex Set TauCeti StrictConvexBilliardTable

namespace TauCeti.Examples.BilliardOrientedLine

attribute [local instance] Complex.finrank_real_complex_fact

variable {R : ℝ} (hR : 0 < R)

/-- On the circular table the state `(0, 0)` has the oriented line `(-1, 0)`: the horizontal line
through the origin, oriented towards `-1`. -/
theorem orientedLine_circle_zero : (circle hR).orientedLine 0 0 = (-1, 0) := by
  have hu : (circle hR).outgoingDir 0 0 = -1 := by
    rw [outgoingDir_def, deriv_circle, zero_div]
    simp [Complex.rightAngleRotation, circleMap]
  rw [orientedLine_def, hu, circle_apply, Complex.areaForm]
  simp [circleMap]

/-- Time reversal at the next collision point reverses the line: `Λ(ι(B(0, 0))) = (1, 0)`. -/
theorem orientedLine_circle_reverse :
    (circle hR).orientedLine ((circle hR).nextParam 0 0) (-(circle hR).nextTangential 0 0) =
      (1, 0) := by
  rw [orientedLine_nextParam_neg_nextTangential _ (by norm_num), orientedLine_circle_zero hR]
  simp

end TauCeti.Examples.BilliardOrientedLine
