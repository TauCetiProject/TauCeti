/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Basic facts about the real logarithm

* `Real.log_div_pos`: for `0 < r < c` the logarithm `log (c / r)` is positive.
-/

public section

namespace Real

/-- For `0 < r < c` the logarithm `log (c / r)` is positive. -/
theorem log_div_pos {c r : ℝ} (h0 : 0 < r) (hr : r < c) : 0 < log (c / r) :=
  log_pos ((one_lt_div h0).2 hr)

end Real
