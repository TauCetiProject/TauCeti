/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-!
# Continuity of stopped paths

Stopping a continuous path preserves continuity, including when the stopping time is infinite.
This pathwise fact requires no measurability or stopping-time hypothesis and lets continuous
local-martingale arguments retain the path regularity of their native stopped stages.
-/

public section

/-- Stopping preserves continuity of each path, without any measurability assumption on the
random time. At an infinite stopping time the path is unchanged. -/
theorem Continuous.stoppedProcess {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω}
    (hX : Continuous (X · ω)) :
    Continuous (MeasureTheory.stoppedProcess X τ · ω) := by
  cases hτ : τ ω with
  | top => simpa [MeasureTheory.stoppedProcess, hτ] using hX
  | coe t =>
    simpa only [MeasureTheory.stoppedProcess, hτ, ← WithTop.coe_min, WithTop.untopA,
      WithTop.untopD_coe, Function.comp_def, id_eq] using
      hX.comp (continuous_id.min (continuous_const (y := t)))
