/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Limits of the real exponential at zero

Mathlib records `Real.tendsto_exp_nhds_zero_nhds_one : exp u → 1` as `u → 0`. This file adds
the scaled form `c e^{a u} → c`, which is how a discount factor `K e^{-r τ}` approaches the
undiscounted amount `K` as the time `τ` tends to `0`.

## Main declarations

* `Real.tendsto_mul_exp_mul_nhds_zero`: `c e^{a u} → c` as `u → 0`.
-/

public section

open Filter
open scoped Topology

namespace Real

/-- For all `c` and `a`, `c e^{a u}` tends to `c` as `u → 0`. -/
theorem tendsto_mul_exp_mul_nhds_zero (c a : ℝ) :
    Tendsto (fun u => c * exp (a * u)) (𝓝 0) (𝓝 c) := by
  have h : Continuous fun u => c * exp (a * u) := by fun_prop
  simpa using h.tendsto 0

end Real
