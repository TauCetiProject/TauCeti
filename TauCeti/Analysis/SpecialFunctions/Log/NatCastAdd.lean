/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The divergence of `log (N + c)` along the natural numbers

For any real shift `c`, the logarithms `log (N + c)` of the shifted natural numbers tend to `+∞`.
At `c = 1` these are the cutoffs `log (N + 1)` at which the Laplace transform of the step function
`t ↦ a ⌊exp t⌋₊` is a partial sum of the Dirichlet series of `a`.

## Main results

* `Real.tendsto_log_natCast_add_atTop` — `log (N + c)` tends to `atTop` as `N → ∞`.
-/

public section

namespace Real

open Filter

/-- For any real shift `c`, `log (N + c)` tends to `+∞` as the natural number `N` does. -/
theorem tendsto_log_natCast_add_atTop (c : ℝ) :
    Tendsto (fun N : ℕ ↦ log (N + c)) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

end Real
