/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The reparametrisation `s ↦ log s - log (1 - s)` of the open unit interval

The map `s ↦ log s - log (1 - s)` is continuous on the open unit interval `(0, 1)` and tends to
`-∞` at its left end and to `+∞` at its right end, so it reparametrises the open unit interval by
the real line. A curve `ℝ → X` with limits at `±∞`, read along it, extends to a path on the closed
unit interval.

## Main results

* `Real.continuousOn_log_sub_log_one_sub`: continuity on `(0, 1)`.
* `Real.tendsto_log_sub_log_one_sub_nhdsGT_zero`: the limit `-∞` as `s` decreases to `0`.
* `Real.tendsto_log_sub_log_one_sub_nhdsLT_one`: the limit `+∞` as `s` increases to `1`.
-/

public section

namespace Real

open Filter Set Topology

/-- The reparametrisation `s ↦ log s - log (1 - s)` of the open unit interval by the real line is
continuous on it. -/
theorem continuousOn_log_sub_log_one_sub :
    ContinuousOn (fun s : ℝ ↦ log s - log (1 - s)) (Ioo 0 1) :=
  ((continuousOn_id (s := Ioo (0 : ℝ) 1)).log fun _ hs ↦ hs.1.ne').sub
    (((continuousOn_const (c := (1 : ℝ))).sub continuousOn_id).log fun _ hs ↦
      (sub_pos.2 hs.2).ne')

/-- The reparametrisation `s ↦ log s - log (1 - s)` tends to `-∞` at the left end of the unit
interval. -/
theorem tendsto_log_sub_log_one_sub_nhdsGT_zero :
    Tendsto (fun s : ℝ ↦ log s - log (1 - s)) (𝓝[>] 0) atBot := by
  have h₁ : Tendsto (fun s : ℝ ↦ 1 - s) (𝓝 0) (𝓝 1) := by
    simpa using (continuous_sub_left (1 : ℝ)).tendsto 0
  have h₂ : Tendsto (fun s : ℝ ↦ -log (1 - s)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((h₁.log one_ne_zero).neg).mono_left nhdsWithin_le_nhds
  simpa only [sub_eq_add_neg] using tendsto_log_nhdsGT_zero.atBot_add h₂

/-- The reparametrisation `s ↦ log s - log (1 - s)` tends to `+∞` at the right end of the unit
interval. -/
theorem tendsto_log_sub_log_one_sub_nhdsLT_one :
    Tendsto (fun s : ℝ ↦ log s - log (1 - s)) (𝓝[<] 1) atTop := by
  have h₁ : Tendsto log (𝓝[<] 1) (𝓝 0) := by
    simpa using (continuousAt_log one_ne_zero).tendsto.mono_left nhdsWithin_le_nhds
  have h₂ : Tendsto (fun s : ℝ ↦ 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun s : ℝ ↦ 1 - s) (𝓝 1) (𝓝 0) := by
        simpa using (continuous_sub_left (1 : ℝ)).tendsto 1
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs using sub_pos.2 hs
  have h₃ : Tendsto (fun s : ℝ ↦ -log (1 - s)) (𝓝[<] 1) atTop :=
    tendsto_neg_atBot_atTop.comp (tendsto_log_nhdsGT_zero.comp h₂)
  simpa only [sub_eq_add_neg] using h₁.add_atTop h₃

end Real
