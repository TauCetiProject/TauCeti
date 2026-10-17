/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup.Finiteness
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType

/-!
# Finiteness of the Suzuki, Ree, and Tits entries

On each of the four half-Frobenius branches, the square of the Steinberg map acts on every
matrix entry by the field-order Frobenius. Thus a fixed point has coordinates in a finite field.
The finite-coordinate criterion proves finiteness of the fixed subgroup; subgroups and quotients
then give finiteness of the exact candidate used by `ValidLieTypeIndex.Group`.

The argument includes the Tits index, whose field exponent is one. It uses the coordinate
formulas on the whole ambient carrier and does not assume root generation, simplicity,
or a recognition theorem.
-/

public section

namespace TauCeti

/-- The Suzuki Steinberg fixed group is finite: its square is the field-order Frobenius on
the four-dimensional symplectic carrier. -/
theorem SuzukiLieIndex.finite_fixedPoints (d : SuzukiLieIndex) : Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup 2 _
    d.steinberg d.1.fieldExponent 2 d.1.fieldExponent_pos.ne'
  intro g i j
  change ((d.steinberg (d.steinberg g) : Matrix.GeneralLinearGroup (Fin 4) d.1.Closure)
    i j) = _
  rw [d.steinberg_steinberg, d.toRankTwoBLieIndex.coe_frobenius_apply,
    d.1.fieldOrder_eq_characteristic_pow]
  simp only [d.characteristic_eq_two]

/-- The Ree `G₂` Steinberg fixed group is finite: its square is the field-order Frobenius on
the seven-dimensional short-root carrier. -/
theorem ReeG2LieIndex.finite_fixedPoints (d : ReeG2LieIndex) : Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup 3 _
    d.steinberg d.1.fieldExponent 2 d.1.fieldExponent_pos.ne'
  intro g i j
  change ((d.steinberg (d.steinberg g) : Matrix.GeneralLinearGroup (Fin 7) d.1.Closure)
    i j) = _
  rw [d.steinberg_steinberg, d.coe_frobenius_apply, d.1.fieldOrder_eq_characteristic_pow]
  simp only [d.characteristic_eq_three]

/-- The Ree `F₄` Steinberg fixed group is finite: its square is the field-order Frobenius on
the twenty-six-dimensional short-root carrier. -/
theorem ReeF4LieIndex.finite_fixedPoints (d : ReeF4LieIndex) : Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup 2 _
    d.steinberg d.1.fieldExponent 2 d.1.fieldExponent_pos.ne'
  intro g i j
  change ((d.steinberg (d.steinberg g) : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure)
    i j) = _
  rw [d.steinberg_steinberg, d.coe_frobenius_apply, d.1.fieldOrder_eq_characteristic_pow]
  simp only [d.characteristic_eq_two]

/-- The exceptional `F₄` endomorphism at the Tits index has finitely many fixed points,
since its square squares every matrix entry. -/
theorem TitsLieIndex.finite_fixedPoints (d : TitsLieIndex) : Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup 2 _
    d.steinberg 1 2 (by decide)
  intro g i j
  change ((d.steinberg (d.steinberg g) : Matrix.GeneralLinearGroup (Fin 26) d.1.Closure)
    i j) = _
  rw [d.steinberg_steinberg, d.coe_frobenius_apply, pow_one]

/-- The assembled Steinberg fixed group is finite on each of the four half-Frobenius
branches: Suzuki, the two Ree families, and Tits. -/
theorem ValidLieTypeIndex.finite_fixedPoints_of_usesHalfFrobenius (d : ValidLieTypeIndex)
    (h : d.1.UsesHalfFrobenius) : Finite d.FixedPoints := by
  obtain ⟨d, hv⟩ := d
  cases d
  all_goals try { simp [LieTypeIndex.usesHalfFrobenius_iff] at h }
  all_goals simp only [ValidLieTypeIndex.FixedPoints, ValidLieTypeIndex.steinberg_suzuki,
    ValidLieTypeIndex.steinberg_reeG2, ValidLieTypeIndex.steinberg_reeF4,
    ValidLieTypeIndex.steinberg_tits]
  · exact SuzukiLieIndex.finite_fixedPoints ⟨⟨_, hv⟩, by simp⟩
  · exact ReeG2LieIndex.finite_fixedPoints ⟨⟨_, hv⟩, by simp⟩
  · exact ReeF4LieIndex.finite_fixedPoints ⟨⟨_, hv⟩, by simp⟩
  · exact TitsLieIndex.finite_fixedPoints ⟨⟨_, hv⟩, by simp⟩

/-- The exact assembled CFSG candidate is finite on each half-Frobenius branch, by finiteness
of its fixed group, derived subgroup, and central quotient. -/
theorem ValidLieTypeIndex.finite_group_of_usesHalfFrobenius (d : ValidLieTypeIndex)
    (h : d.1.UsesHalfFrobenius) : Finite d.Group := by
  have := d.finite_fixedPoints_of_usesHalfFrobenius h
  infer_instance

end TauCeti
