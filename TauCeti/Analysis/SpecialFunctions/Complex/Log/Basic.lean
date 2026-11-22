/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Local branch identities for the complex principal logarithm

When `p₀` lies in `Complex.slitPlane`, its argument lies strictly in `(-π, π)`. Multiplying `p₀`
by a perturbation `1 + u x` with `u → 0` shifts the argument by an amount tending to `0`, so the
sum of arguments eventually stays in `(-π, π]` and the principal logarithm splits locally as
`Complex.log (p₀ * (1 + u x)) = Complex.log p₀ + Complex.log (1 + u x)`.

## Main results

* `Complex.eventually_log_mul_one_add`: for `p₀ ∈ Complex.slitPlane` and `u → 0` along a filter,
  eventually `Complex.log (p₀ * (1 + u x)) = Complex.log p₀ + Complex.log (1 + u x)`.
-/

public section

open Filter Topology
open scoped Real

namespace Complex

/-- Local branch law for the principal complex logarithm: when `p₀ ∈ Complex.slitPlane` and
`u → 0` along `l`, eventually
`Complex.log (p₀ * (1 + u x)) = Complex.log p₀ + Complex.log (1 + u x)`. -/
theorem eventually_log_mul_one_add {α : Type*} {l : Filter α} {p₀ : ℂ}
    (hp₀ : p₀ ∈ slitPlane) {u : α → ℂ} (hu : Tendsto u l (𝓝 0)) :
    ∀ᶠ x in l, log (p₀ * (1 + u x)) = log p₀ + log (1 + u x) := by
  have harg_ne : p₀.arg ≠ π := (mem_slitPlane_iff_arg.mp hp₀).1
  have hp₀_ne : p₀ ≠ 0 := (mem_slitPlane_iff_arg.mp hp₀).2
  have harg_lt : p₀.arg < π := lt_of_le_of_ne (arg_le_pi p₀) harg_ne
  have harg_gt : -π < p₀.arg := neg_pi_lt_arg p₀
  set ε : ℝ := min (π - p₀.arg) (p₀.arg + π)
  have hε : 0 < ε := lt_min (sub_pos.mpr harg_lt) (by linarith)
  have h1u : Tendsto (fun x => 1 + u x) l (𝓝 (1 : ℂ)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hu
  have harg1u : Tendsto (fun x => (1 + u x).arg) l (𝓝 0) := by
    simpa only [arg_one, Function.comp_def] using
      (continuousAt_arg one_mem_slitPlane).tendsto.comp h1u
  filter_upwards [h1u.eventually_ne one_ne_zero, harg1u.eventually (Metric.ball_mem_nhds 0 hε)]
    with x hxne hxarg
  rw [log_mul_eq_add_log_iff hp₀_ne hxne]
  rw [Real.dist_eq, sub_zero, abs_lt] at hxarg
  have hε1 : ε ≤ π - p₀.arg := min_le_left _ _
  have hε2 : ε ≤ p₀.arg + π := min_le_right _ _
  exact ⟨by linarith, by linarith⟩

end Complex
