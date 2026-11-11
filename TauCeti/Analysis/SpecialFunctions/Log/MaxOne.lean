/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Nonnegativity of the logarithm of a lower-truncated number

The logarithm of `max 1 x` is nonnegative for every real `x`. It absorbs constant terms in
estimates of the form `C * (1 + log (max 1 |b|))`.

## Main results

* `Real.log_max_one_nonneg`: `0 ≤ log (max 1 x)`.
-/

public section

namespace Real

/-- The logarithm of `max 1 x` is nonnegative for every real `x`. -/
@[simp] theorem log_max_one_nonneg (x : ℝ) : 0 ≤ log (max 1 x) :=
  log_nonneg (le_max_left _ _)

end Real
