/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE
-/
module

public import TauCeti.Algebra.Order.Ring.Units
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import TauCeti.Topology.Algebra.Group.Connected
public import TauCeti.Topology.Algebra.Group.Units

/-!
# The identity component of the positive real units

The positive units of `ℝ` are the identity component of the real unit group. The proof identifies
the positive units with the image of the positive half-line under the continuous unit constructor.
-/

public section

open Set

namespace Units

/-- The positive real units form a preconnected set. -/
theorem isPreconnected_posSubgroup_real :
    IsPreconnected (Units.posSubgroup ℝ : Set ℝˣ) := by
  let f : Set.Ioi (0 : ℝ) → Units.posSubgroup ℝ := fun x =>
    ⟨Units.mk0 x.1 x.2.ne', (Units.mem_posSubgroup _).2 x.2⟩
  have hf : Continuous f := by
    apply continuous_induced_rng.mpr
    apply Units.continuous_iff.mpr
    constructor
    · exact continuous_subtype_val
    · apply continuous_iff_continuousAt.mpr
      intro x
      apply ContinuousAt.congr_of_eventuallyEq
        ((continuousAt_inv₀ x.2.ne').comp continuous_subtype_val.continuousAt)
      filter_upwards [] with y
      rfl
  let hpreIoi : PreconnectedSpace (Set.Ioi (0 : ℝ)) :=
    Subtype.preconnectedSpace isPreconnected_Ioi
  have himage : f '' (Set.univ : Set (Set.Ioi (0 : ℝ))) =
      (Set.univ : Set (Units.posSubgroup ℝ)) := by
    ext u
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp
    · intro hu
      let x : Set.Ioi (0 : ℝ) :=
        ⟨(((u : Units.posSubgroup ℝ) : ℝˣ) : ℝ),
          (Units.mem_posSubgroup _).1 u.2⟩
      refine ⟨x, mem_univ _, ?_⟩
      apply Subtype.ext
      simp [f, x]
  let hprePos : PreconnectedSpace (Units.posSubgroup ℝ) := by
    refine ⟨?_⟩
    have h := (@PreconnectedSpace.isPreconnected_univ (Set.Ioi (0 : ℝ)) _ hpreIoi).image
      f hf.continuousOn
    rw [himage] at h
    exact h
  exact isPreconnected_iff_preconnectedSpace.mpr hprePos

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
