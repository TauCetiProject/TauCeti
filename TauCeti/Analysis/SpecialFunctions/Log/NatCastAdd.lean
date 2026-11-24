/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import TauCeti.Order.Filter.AtTopBot

/-!
# Logarithmic cutoffs along the natural numbers

The logarithms `log (N + c)` of the shifted natural numbers are positive for a real shift
`c > 1`, and tend to `+∞` for any real shift `c`.
The logarithms `log n` cut `(0, ∞)` into the steps `(log n, log (n + 1))`, on each of which the
step function `t ↦ ⌊exp t⌋₊` is constant, equal to `n`. In particular, the logarithmic rounding
discrepancy `t - log ⌊exp t⌋₊` is bounded by `log (1 + 1 / ⌊exp t⌋₊)` and tends to `0` as
`t → +∞`. At the cutoffs `log (N + 1)`, the truncated Laplace integral of `t ↦ a ⌊exp t⌋₊` is
therefore the partial sum of the Dirichlet series of `a` plus the corresponding partial sum of a
step correction.

## Main results

* `Real.log_natCast_add_pos` — `log (N + c)` is positive for every shift `c > 1`.
* `Real.tendsto_log_natCast_add_atTop` — `log (N + c)` tends to `atTop` as `N → ∞`.
* `Real.floor_exp_eq_of_mem_Ioo` — `⌊exp t⌋₊ = n` for `t ∈ (log n, log (n + 1))`.
* `TauCeti.tendsto_sub_log_floor_exp_atTop` — `t - log ⌊exp t⌋₊ → 0` as `t → +∞`.
-/

public section

namespace Real

open Filter Set

/-- For a real shift `c > 1`, `log (N + c)` is positive for every natural number `N`. -/
theorem log_natCast_add_pos {c : ℝ} (hc : 1 < c) (N : ℕ) : 0 < log (N + c) :=
  log_pos (by linarith [N.cast_nonneg (α := ℝ)])

/-- For any real shift `c`, `log (N + c)` tends to `+∞` as the natural number `N` does. -/
theorem tendsto_log_natCast_add_atTop (c : ℝ) :
    Tendsto (fun N : ℕ ↦ log (N + c)) atTop atTop :=
  tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

/-- On the open step `(log n, log (n + 1))`, the floor of `exp t` is `n`. For `n = 0` the step is
empty. -/
theorem floor_exp_eq_of_mem_Ioo {n : ℕ} {t : ℝ}
    (ht : t ∈ Ioo (log n) (log (n + 1))) : ⌊exp t⌋₊ = n := by
  rcases n.eq_zero_or_pos with rfl | hn'
  · simp at ht
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hn'
  have hlo : (n : ℝ) < exp t := by simpa [exp_log hn] using exp_lt_exp.mpr ht.1
  have hhi : exp t < n + 1 := by
    simpa [exp_log (by positivity : (0 : ℝ) < n + 1)] using exp_lt_exp.mpr ht.2
  exact (Nat.floor_eq_iff (exp_pos t).le).mpr ⟨hlo.le, hhi⟩

end Real

namespace TauCeti

open Filter
open scoped Topology

/-- The logarithmic rounding error `t - log ⌊exp t⌋₊` tends to `0` as `t → +∞`. -/
theorem tendsto_sub_log_floor_exp_atTop :
    Tendsto (fun t : ℝ ↦ t - Real.log ⌊Real.exp t⌋₊) atTop (𝓝 0) := by
  have hupper : Tendsto (fun m : ℕ ↦ Real.log (1 + 1 / (m : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ ↦ (1 : ℝ) + 1 / (m : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h1
    simpa [Function.comp_def] using (Real.continuousAt_log one_ne_zero).tendsto.comp h1
  have hupper_exp : Tendsto (fun t : ℝ ↦ Real.log (1 + 1 / (⌊Real.exp t⌋₊ : ℝ))) atTop (𝓝 0) :=
    (tendsto_comp_natFloor_iff.mpr hupper).comp Real.tendsto_exp_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper_exp ?_ ?_
  · filter_upwards [eventually_ge_atTop 0] with t ht
    have hm1 : 1 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp ht)
    have hm_pos : (0 : ℝ) < ⌊Real.exp t⌋₊ := Nat.cast_pos.mpr hm1
    have hle : Real.log ⌊Real.exp t⌋₊ ≤ t :=
      (Real.log_le_iff_le_exp hm_pos).mpr (Nat.floor_le (Real.exp_nonneg t))
    linarith
  · filter_upwards [eventually_ge_atTop 0] with t ht
    have hm1 : 1 ≤ ⌊Real.exp t⌋₊ := Nat.le_floor (by simpa using Real.one_le_exp ht)
    have hm_pos : (0 : ℝ) < ⌊Real.exp t⌋₊ := Nat.cast_pos.mpr hm1
    have hlt : t ≤ Real.log (⌊Real.exp t⌋₊ + 1) := by
      simpa only [Real.log_exp] using
        Real.log_le_log (Real.exp_pos t) (Nat.lt_floor_add_one (Real.exp t)).le
    have hlog : Real.log (⌊Real.exp t⌋₊ + 1) - Real.log ⌊Real.exp t⌋₊ =
        Real.log (1 + 1 / (⌊Real.exp t⌋₊ : ℝ)) := by
      rw [← Real.log_div (by positivity) hm_pos.ne', add_div, div_self hm_pos.ne']
    linarith

end TauCeti
