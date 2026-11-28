/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Limits of the complex exponential

As `Re ζ → +∞`, `exp ζ` tends to infinity (Mathlib's `Complex.tendsto_exp_comap_re_atTop`), so
`exp (-ζ)` tends to `0`. In the logarithmic coordinate `z = exp ζ` this is `z⁻¹ → 0` as
`z → ∞`. For `u, v : ℂ`, `(1 + u / N) ^ N / (1 + v / N) ^ N → exp (u - v)` as `N → ∞`.

## Main results

* `Complex.tendsto_exp_neg_comap_re_atTop`: `exp (-ζ) → 0` as `Re ζ → +∞`.
* `Complex.tendsto_one_add_div_pow_div_exp`: `(1 + u / N) ^ N / (1 + v / N) ^ N → exp (u - v)`.
-/

public section

open Filter
open scoped Topology

namespace Complex

/-- `exp (-ζ)` tends to `0` as `Re ζ → +∞`. -/
theorem tendsto_exp_neg_comap_re_atTop :
    Tendsto (fun ζ ↦ exp (-ζ)) (comap re atTop) (𝓝 0) := by
  simpa only [Function.comp_def, exp_neg] using
    tendsto_inv₀_cobounded.comp tendsto_exp_comap_re_atTop

/-- As `N → ∞`, `(1 + u / N) ^ N / (1 + v / N) ^ N` converges to `exp (u - v)`. -/
theorem tendsto_one_add_div_pow_div_exp (u v : ℂ) :
    Tendsto (fun N : ℕ ↦ (1 + u / N) ^ N / (1 + v / N) ^ N) atTop (𝓝 (exp (u - v))) :=
  exp_sub u v ▸ (tendsto_one_add_div_pow_exp u).div (tendsto_one_add_div_pow_exp v)
    (exp_ne_zero _)

end Complex
