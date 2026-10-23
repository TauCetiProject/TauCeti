/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Ring.Units
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import TauCeti.Topology.Algebra.Group.Connected
public import TauCeti.Topology.Algebra.Group.Units

/-!
# The identity component of the real unit group

The positive units of `ℝ` form the identity component of the real unit group. This file provides
their preconnectedness and identifies `Subgroup.connectedComponentOfOne ℝˣ` with
`Units.posSubgroup ℝ`.
-/

public section

open Set

namespace Units

/-- The positive real units form a preconnected set. -/
theorem isPreconnected_posSubgroup_real :
    IsPreconnected (Units.posSubgroup ℝ : Set ℝˣ) := by
  have hcarrier : (Units.posSubgroup ℝ : Set ℝˣ) = Units.val ⁻¹' Set.Ioi (0 : ℝ) := by
    ext u
    exact Units.mem_posSubgroup u
  rw [hcarrier]
  exact isPreconnected_Ioi.preimage_units_val (by simp : (0 : ℝ) ∉ Set.Ioi 0)

/-- The positive real units are the identity component of the real unit group. -/
theorem connectedComponentOfOne_real :
    Subgroup.connectedComponentOfOne ℝˣ = Units.posSubgroup ℝ := by
  apply le_antisymm
  · apply Subgroup.connectedComponentOfOne_le_of_isOpen
    rw [isOpen_iff_mem_nhds]
    intro u hu
    have hval : (0 : ℝ) < (u : ℝ) := (Units.mem_posSubgroup _).1 hu
    exact IsOpen.mem_nhds (isOpen_Ioi.preimage Units.continuous_val) hval
  · intro u hu
    exact isPreconnected_posSubgroup_real.subset_connectedComponent (by simp) hu

end Units
