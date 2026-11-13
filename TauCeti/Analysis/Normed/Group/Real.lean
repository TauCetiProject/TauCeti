/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Real

/-!
# Squared extended norms of real numbers

`Real.enorm_sq_eq_ofReal_sq` converts a squared extended norm into the nonnegative
real square embedded in `ℝ≥0∞`, for use in lower-integral energy identities.
-/

public section

open scoped ENNReal

namespace Real

/-- The squared extended norm of a real number is its square embedded in `ℝ≥0∞`. -/
theorem enorm_sq_eq_ofReal_sq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [eNorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

end Real
