/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.GraphTwisted
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.HalfFrobenius
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Type.A
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Type.BC
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Type.DE
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.Unimodular

/-!
# Finiteness of every Lie-type candidate on the CFSG list

The family finiteness theorems cover all seventeen valid Lie-type constructors, including
the graph-twisted, Suzuki, Ree, and Tits entries. The assembly's branch equations identify
their fixed groups with the exact carriers used by `ValidLieTypeIndex.FixedPoints`.
Taking the derived subgroup and its central quotient then proves
`ValidLieTypeIndex.finite_group`.
-/

public section

namespace TauCeti

/-- The Steinberg fixed group is finite on every ordinary or graph-twisted Lie-type index. -/
theorem GraphTwistedIndex.finite_fixedPoints (d : GraphTwistedIndex) : Finite d.FixedPoints := by
  obtain ⟨⟨d, hv⟩, h⟩ := d
  cases d
  all_goals try { simp [LieTypeIndex.usesHalfFrobenius_iff] at h }
  all_goals change Finite ↥(fixedSubgroup _)
  · rw [GraphTwistedIndex.steinberg_A]
    exact TypeALieIndex.finite_fixedPoints _
  · rw [GraphTwistedIndex.steinberg_twistedA]
    exact TypeALieIndex.finite_fixedPoints _
  · rw [GraphTwistedIndex.steinberg_B]
    exact TypeBLieIndex.finite_fixedPoints _
  · rw [GraphTwistedIndex.steinberg_C]
    exact TypeCLieIndex.finite_fixedPoints _
  · rw [GraphTwistedIndex.steinberg_D]
    exact TypeDLieIndex.finite_fixedSubgroup_steinberg ⟨⟨_, hv⟩, by simp⟩
  · rw [GraphTwistedIndex.steinberg_twistedD]
    exact TypeTwistedDLieIndex.finite_fixedPoints ⟨⟨_, hv⟩, by simp⟩
  · rw [GraphTwistedIndex.steinberg_E6]
    exact TypeE6LieIndex.finite_fixedSubgroup_steinberg _
  · rw [GraphTwistedIndex.steinberg_E7]
    exact TypeE7LieIndex.finite_fixedSubgroup_steinberg _
  · rw [GraphTwistedIndex.steinberg_E8]
    exact UnimodularExceptionalIndex.finite_fixedPoints _
  · rw [GraphTwistedIndex.steinberg_F4]
    exact UnimodularExceptionalIndex.finite_fixedPoints _
  · rw [GraphTwistedIndex.steinberg_G2]
    exact UnimodularExceptionalIndex.finite_fixedPoints _
  · rw [GraphTwistedIndex.steinberg_twistedE6]
    exact TypeTwistedE6LieIndex.finite_fixedPoints _
  · rw [GraphTwistedIndex.steinberg_trialityD4]
    exact TypeTrialityD4LieIndex.finite_fixedPoints _

/-- The exact assembled Steinberg fixed group is finite for every valid Lie-type index. -/
theorem ValidLieTypeIndex.finite_fixedPoints (d : ValidLieTypeIndex) : Finite d.FixedPoints := by
  by_cases h : d.1.UsesHalfFrobenius
  · exact d.finite_fixedPoints_of_usesHalfFrobenius h
  · rw [d.FixedPoints_eq_of_not_usesHalfFrobenius h]
    exact GraphTwistedIndex.finite_fixedPoints ⟨d, h⟩

/-- Every Lie-type candidate on the CFSG list is finite, as a central quotient of the derived
subgroup of its finite Steinberg fixed group. -/
theorem ValidLieTypeIndex.finite_group (d : ValidLieTypeIndex) : Finite d.Group := by
  have := d.finite_fixedPoints
  infer_instance

end TauCeti
