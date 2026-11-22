/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog

/-!
# Scaled logarithms of extended nonnegative reals

`TauCeti.ENNReal.coe_mul_log_monotone`: at a nonnegative multiplier `e`, the scaled logarithm
`x ↦ e * log x` from `ℝ≥0∞` to `EReal` is monotone. Exponential rates `e * log (μ A)`, as in large
deviations, are therefore monotone in the set `A`.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

/-- At a nonnegative multiplier `e`, the scaled logarithm `x ↦ e * log x` is monotone. -/
theorem ENNReal.coe_mul_log_monotone (e : ℝ≥0) :
    Monotone fun x : ℝ≥0∞ => ((e : ℝ) : EReal) * ENNReal.log x :=
  fun _ _ h => mul_le_mul_of_nonneg_left (ENNReal.log_monotone h) (by exact_mod_cast e.coe_nonneg)

end TauCeti
