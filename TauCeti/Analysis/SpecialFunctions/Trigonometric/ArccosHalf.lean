/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# `arccos` at `±1/2`

Mathlib records `Real.cos_pi_div_three : cos (π / 3) = 1 / 2` but not the corresponding values
of `Real.arccos`. This file records them in the same shape.

## Main results

* `Real.arccos_one_half`: `arccos (1 / 2) = π / 3`.
* `Real.arccos_neg_one_half`: `arccos (-(1 / 2)) = 2π / 3`.
-/

public section

namespace Real

/-- `arccos (1 / 2) = π / 3`. -/
theorem arccos_one_half : arccos (1 / 2) = π / 3 := by
  rw [← cos_pi_div_three, arccos_cos (by positivity) (by linarith [pi_pos])]

/-- `arccos (-(1 / 2)) = 2π / 3`. -/
theorem arccos_neg_one_half : arccos (-(1 / 2)) = 2 * π / 3 := by
  rw [arccos_neg, arccos_one_half]
  ring

end Real
