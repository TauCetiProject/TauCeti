/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv

/-!
# The difference quotient of a complex exponential at `0`

For `c : ℂ`, the function `t ↦ exp (c t)` of a real variable has derivative `c` at `0`. This file
records that derivative in the difference-quotient form

`t⁻¹ • (exp (c t) - 1) → c` as `t → 0`, `t ≠ 0`.

Restricting to `t → 0⁺` (via `nhdsGT_le_nhdsNE`) gives the shape a generator difference quotient
takes: the semigroup parameter of a C₀-semigroup runs over the nonnegative reals, so its
generator is a limit along `𝓝[>] 0`.

## Main results

* `TauCeti.tendsto_inv_smul_exp_mul_ofReal_sub_one`: the difference quotient of
  `t ↦ exp (c t)` at `0` tends to `c`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- The difference quotient of `t ↦ exp (c t)` at `0`, taken along the punctured real line,
tends to `c`: the derivative of a complex exponential at the origin. -/
theorem tendsto_inv_smul_exp_mul_ofReal_sub_one (c : ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ • (Complex.exp (c * t) - 1)) (𝓝[≠] (0 : ℝ)) (𝓝 c) := by
  simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c).cexp.tendsto_slope_zero

end TauCeti

end
