/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The logarithm of `π`

* `Real.log_pi_pos`: `log π` is positive, since `π ≥ 2 > 1`.
-/

public section

namespace Real

/-- `log π` is positive. -/
theorem log_pi_pos : 0 < log π := log_pos (by linarith [two_le_pi])

end Real
