/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Limits of the real exponential

Mathlib records `Real.tendsto_exp_nhds_zero_nhds_one : exp u → 1` as `u → 0`. This file adds
the scaled form `c e^{a u} → c`, which is how a discount factor `K e^{-r τ}` approaches the
undiscounted amount `K` as the time `τ` tends to `0`, and the first-order limit
`(e^{a t} - 1) / t → a`, the difference quotient of `t ↦ e^{a t}` at zero, which identifies the
generator of an exponentially rescaled semigroup. It also records that `e^{t - k} → 0` along the
natural numbers `k`.

## Main declarations

* `Real.tendsto_mul_exp_mul_nhds_zero`: `c e^{a u} → c` as `u → 0`.
* `Real.tendsto_exp_mul_sub_one_div`: `(e^{a t} - 1) / t → a` as `t → 0`, `t ≠ 0`.
* `Real.tendsto_exp_sub_natCast_atTop_nhds_zero`: `e^{t - k} → 0` as `k → ∞` in `ℕ`.
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

/-- The difference quotient `(e^{a t} - 1) / t` of `t ↦ e^{a t}` at zero tends to `a` as
`t → 0` with `t ≠ 0`. -/
theorem tendsto_exp_mul_sub_one_div (a : ℝ) :
    Tendsto (fun t => (exp (a * t) - 1) / t) (𝓝[≠] 0) (𝓝 a) := by
  simpa [div_eq_inv_mul] using ((hasDerivAt_id (0 : ℝ)).const_mul a).exp.tendsto_slope_zero

/-- For every `t`, `e^{t - k}` tends to `0` as the natural number `k` tends to infinity. -/
theorem tendsto_exp_sub_natCast_atTop_nhds_zero (t : ℝ) :
    Tendsto (fun k : ℕ ↦ exp (t - k)) atTop (𝓝 0) := by
  refine tendsto_exp_atBot.comp ?_
  simp only [sub_eq_add_neg]
  exact tendsto_atBot_add_const_left _ t (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)

end Real
