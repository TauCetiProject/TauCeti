/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Analysis.SpecialFunctions.Exp.Periodic

/-!
# Regularity of the centered complex logarithm branch

For any nonzero `z₀ : ℂ`, the centered branch `z ↦ Complex.log z₀ + Complex.log (z / z₀)` avoids
the principal branch cut near `z₀`, so it is `C^n` (over `ℂ`, hence holomorphic) at `z₀` even when
`z₀` lies on the nonpositive real axis, and satisfies `exp (log z₀ + log (z / z₀)) = z` for every
`z ≠ 0` (`Complex.exp_log_add_log_div`).

## Main declarations

* `Complex.contDiffAt_log_add_log_div`: the centered logarithm branch is `C^n` at `z₀ ≠ 0`.
-/

public section

namespace Complex

/-- The centered branch `z ↦ log z₀ + log (z / z₀)` is `C^n` (over `ℂ`, hence holomorphic) at any
nonzero `z₀`, even when `z₀` lies on the principal branch cut. -/
theorem contDiffAt_log_add_log_div {z₀ : ℂ} (hz₀ : z₀ ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℂ n (fun z : ℂ ↦ log z₀ + log (z / z₀)) z₀ :=
  contDiffAt_const.add
    ((contDiffAt_log (by rw [div_self hz₀]; exact one_mem_slitPlane)).comp z₀
      (contDiffAt_id.div_const z₀))

end Complex
