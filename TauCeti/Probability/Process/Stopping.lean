/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Stopping

/-!
# Stopping times and stopped paths

A stopping time remains a stopping time for a larger filtration. This transports stopping
arguments and localizing sequences when augmenting a filtration.

Stopping preserves right continuity at each time, including when the stopping time is infinite.
This pathwise fact requires no measurability or stopping-time hypothesis and lets local-martingale
arguments retain the right continuity of their native stopped stages.
-/

public section

namespace MeasureTheory.IsStoppingTime

/-- A stopping time for a filtration is also a stopping time for any larger filtration. -/
theorem mono_filtration {ι Ω : Type*} [Preorder ι] {mΩ : MeasurableSpace Ω}
    {ℱ 𝒢 : Filtration ι mΩ} {τ : Ω → WithTop ι}
    (hτ : IsStoppingTime ℱ τ) (h : ℱ ≤ 𝒢) : IsStoppingTime 𝒢 τ :=
  fun t => h t _ (hτ.measurableSet_le t)

end MeasureTheory.IsStoppingTime

open Filter Set
open scoped Topology

/-- Stopping preserves right continuity of a path at a given time, without any measurability
assumption on the random time. At an infinite stopping time the path is unchanged. -/
theorem ContinuousWithinAt.stoppedProcess {ι Ω E : Type*} [LinearOrder ι] [Nonempty ι]
    [TopologicalSpace ι] [OrderTopology ι] [TopologicalSpace E]
    {X : ι → Ω → E} {τ : Ω → WithTop ι} {ω : Ω} {t : ι}
    (hX : ContinuousWithinAt (X · ω) (Ioi t) t) :
    ContinuousWithinAt (MeasureTheory.stoppedProcess X τ · ω) (Ioi t) t := by
  cases hτ : τ ω with
  | top => simpa [MeasureTheory.stoppedProcess, hτ] using hX
  | coe u =>
    by_cases htu : t < u
    · refine hX.congr_of_eventuallyEq ?_ ?_
      · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds htu)] with s hs
        exact MeasureTheory.stoppedProcess_eq_of_le (by simpa [hτ] using hs.le)
      · exact MeasureTheory.stoppedProcess_eq_of_le (by simpa [hτ] using htu.le)
    · have hut : u ≤ t := le_of_not_gt htu
      refine (continuousWithinAt_const (b := X (τ ω).untopA ω)).congr
        (fun s hs => ?_) ?_
      · exact MeasureTheory.stoppedProcess_eq_of_ge (by simpa [hτ] using hut.trans hs.le)
      · exact MeasureTheory.stoppedProcess_eq_of_ge (by simpa [hτ] using hut)
