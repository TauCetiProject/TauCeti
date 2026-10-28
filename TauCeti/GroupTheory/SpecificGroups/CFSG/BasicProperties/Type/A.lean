/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.Finiteness
public import TauCeti.Algebra.Lie.SpecialLinear.StandardCarrier.FixedPoints
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

/-!
# Finiteness of the type-A entries on the CFSG list

The fixed groups attached to both `A_r(q)` and `²A_r(q)` are finite. This gives finiteness of their
derived central quotients through the existing instances for subgroups and quotients.
`TauCeti.TypeALieIndex.finite_group` transfers the result to the exact assembled carrier
`ValidLieTypeIndex.Group` used by the classification statement.

The proof uses the positive field exponent of the validated index and the coordinate formulas for
the entire carrier Frobenius. No simplicity or classification result is assumed.
-/

public section

namespace TauCeti.TypeALieIndex

/-- Both ordinary and twisted type-A Steinberg fixed groups are finite. -/
theorem finite_fixedPoints (d : TypeALieIndex) : Finite d.FixedPoints := by
  change Finite ↥(fixedSubgroup d.steinberg)
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · rw [steinberg_ofA]
    exact SlStd.finite_fixedSubgroup_frobenius_of_charP _ _ _
      (ofA rank q hvalid).1.fieldExponent_pos.ne'
  · rw [steinberg_ofTwistedA]
    exact SlStd.finite_fixedSubgroup_twistedFrobenius _ _ _ _
      (ofTwistedA rank q hvalid).1.fieldExponent_pos.ne'

/-- The exact assembled Lie-type carrier on the CFSG list is finite on both type-A families. -/
theorem finite_group (d : TypeALieIndex) : Finite d.1.Group := by
  rw [ValidLieTypeIndex.Group_eq_of_not_usesHalfFrobenius d.1
    (LieTypeIndex.not_usesHalfFrobenius_of_isTypeA d.2)]
  rcases d.exists_eq_ofA_or_exists_eq_ofTwistedA with
    ⟨rank, q, hvalid, rfl⟩ | ⟨rank, q, hvalid, rfl⟩
  · change Finite (FixedPointCandidate _)
    rw [GraphTwistedIndex.steinberg_A]
    change Finite (ofA rank q hvalid).Group
    have := finite_fixedPoints (ofA rank q hvalid)
    infer_instance
  · change Finite (FixedPointCandidate _)
    rw [GraphTwistedIndex.steinberg_twistedA]
    change Finite (ofTwistedA rank q hvalid).Group
    have := finite_fixedPoints (ofTwistedA rank q hvalid)
    infer_instance

end TauCeti.TypeALieIndex
