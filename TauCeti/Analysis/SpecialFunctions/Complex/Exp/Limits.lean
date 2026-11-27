/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Limits of the complex exponential at `Re ζ → +∞`

As `Re ζ → +∞`, `exp ζ` tends to infinity (Mathlib's `Complex.tendsto_exp_comap_re_atTop`), so
`exp (-ζ)` tends to `0`. In the logarithmic coordinate `z = exp ζ` this is `z⁻¹ → 0` as
`z → ∞`.

## Main results

* `Complex.tendsto_exp_neg_comap_re_atTop`: `exp (-ζ) → 0` as `Re ζ → +∞`.
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

end Complex
