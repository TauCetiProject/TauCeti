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
# The difference quotient of a complex exponential at `0`, along the positive reals

For `c : ℂ`, the function `t ↦ exp (c t)` of a real variable has derivative `c` at `0`. This file
records that derivative in the one-sided difference-quotient form

`t⁻¹ • (exp (c t) - 1) → c` as `t → 0⁺`,

which is the shape a generator difference quotient takes: the semigroup parameter of a
C₀-semigroup runs over the nonnegative reals, so its generator is a limit along `𝓝[>] 0`.

## Main results

* `TauCeti.tendsto_inv_smul_exp_mul_ofReal_sub_one`: the one-sided difference quotient of
  `t ↦ exp (c t)` at `0` tends to `c`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

/-- The difference quotient of `t ↦ exp (c t)` at `0`, taken along the positive reals, tends to
`c`: the derivative of a complex exponential at the origin, one-sidedly. -/
theorem tendsto_inv_smul_exp_mul_ofReal_sub_one (c : ℂ) :
    Tendsto (fun t : ℝ => t⁻¹ • (Complex.exp (c * t) - 1)) (𝓝[>] (0 : ℝ)) (𝓝 c) := by
  have hderiv : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) c 0 := by
    have h : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul c
    simpa using h.cexp
  refine ((hasDerivAt_iff_tendsto_slope.mp hderiv).mono_left
    (nhdsWithin_mono _ fun t ht => ne_of_gt ht)).congr fun t => ?_
  simp [slope_def_module]

end TauCeti

end
