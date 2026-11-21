/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Cadlag

/-!
# Càdlàg step functions

A step taking its new value at its jump time is càdlàg. This supplies the path
regularity of indicators of closed stochastic rays, including a jump at time zero.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

/-- A single step, with the right-hand value at the jump, is càdlàg. -/
theorem isCadlag_ite_le {ι E : Type*} [LinearOrder ι] [TopologicalSpace ι]
    [OrderClosedTopology ι] [TopologicalSpace E] (a : ι) (x y : E) :
    IsCadlag (fun t => if a ≤ t then x else y) := by
  constructor
  · intro t
    by_cases hat : a ≤ t
    · apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [hat.trans (le_of_lt hs), hat]
    · apply tendsto_const_nhds.congr'
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_of_not_ge hat))] with s hs
      simp [not_le.mpr hs, hat]
  · intro t
    by_cases hat : a < t
    · refine ⟨x, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hat)] with s hs
      simp [hs.le]
    · refine ⟨y, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [self_mem_nhdsWithin] with s hs
      simp [not_le.mpr (hs.trans_le (le_of_not_gt hat))]

end TauCeti
