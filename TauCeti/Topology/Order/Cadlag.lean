/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Cadlag

/-!
# Càdlàg step and monotone functions

A step taking its new value at its jump time is càdlàg, and every monotone right-continuous
function into a conditionally complete linear order with the order topology is càdlàg. On a partial
order, right continuity at a bottom element is full continuity there. At any discontinuity where a
natural-valued monotone path is right-continuous and exceeds some strictly earlier value by at most
one, its left limit is one less than its current value.
-/

public section

open Filter Function Set
open scoped Topology

/-- Right continuity at a bottom element of a partial order implies continuity there. -/
theorem ContinuousWithinAt.continuousAt_of_isBot {α β : Type*} [PartialOrder α]
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {a : α}
    (hf : ContinuousWithinAt f (Ioi a) a) (ha : IsBot a) : ContinuousAt f a := by
  simpa [ha.Ici_eq, continuousWithinAt_univ] using continuousWithinAt_Ioi_iff_Ici.mp hf

namespace Monotone

/-- Every monotone right-continuous function from a linear order into a conditionally complete
linear order (both with the order topology) is càdlàg. -/
theorem isCadlag {α β : Type*} [LinearOrder α] [TopologicalSpace α] [OrderTopology α]
    [ConditionallyCompleteLinearOrder β] [TopologicalSpace β] [OrderTopology β]
    {f : α → β} (hf : Monotone f) (hrc : IsRightContinuous f) : IsCadlag f :=
  ⟨hrc, fun x ↦ ⟨_, hf.tendsto_nhdsLT x⟩⟩

/-- At a discontinuity `x` where a monotone natural-valued function is right-continuous and exceeds
some strictly earlier value by at most one, its left limit is one below its value at `x`. -/
theorem leftLim_add_one_eq_of_not_continuousAt {α : Type*} [LinearOrder α]
    [TopologicalSpace α] [OrderTopology α] {f : α → ℕ} (hf : Monotone f)
    {x : α} (hrc : ContinuousWithinAt f (Ioi x) x) (hx : ¬ ContinuousAt f x)
    (hjump : ∃ s < x, f x ≤ f s + 1) :
    leftLim f x + 1 = f x := by
  obtain ⟨s, hsx, hfs⟩ := hjump
  have hr : rightLim f x = f x := (hf.continuousWithinAt_Ioi_iff_rightLim_eq).mp hrc
  have hne : leftLim f x ≠ f x := fun h ↦
    hx (hf.continuousAt_iff_leftLim_eq_rightLim.mpr (h.trans hr.symm))
  have hlt : leftLim f x < f x := lt_of_le_of_ne (hf.leftLim_le le_rfl) hne
  exact le_antisymm hlt (hfs.trans (Nat.add_le_add_right (hf.le_leftLim hsx) 1))

end Monotone

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
