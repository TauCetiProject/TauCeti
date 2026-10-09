/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup.Finiteness
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE6
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeE7.Frobenius

/-!
# Finiteness of the ordinary type-D, E₆, and E₇ fixed groups

The Steinberg maps of these three families are entrywise Frobenius on their spin or minuscule
carriers. Their fixed points therefore have all coordinates in a finite field.
-/

public section

namespace TauCeti

/-- The spin-carrier fixed group of an ordinary type-D index is finite. -/
theorem TypeDLieIndex.finite_fixedSubgroup_steinberg (d : TypeDLieIndex) :
    Finite ↥(fixedSubgroup d.steinberg) := by
  rw [d.steinberg_def]
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.1.characteristic _
    d.toTypeDDiagramLieIndex.frobenius d.1.fieldExponent 1 d.1.fieldExponent_pos.ne'
  intro g i j
  change (d.toTypeDDiagramLieIndex.frobenius g : Matrix.GeneralLinearGroup
    (Fin (TypeDSpinCarrier.dimension d.1.rank)) d.1.Closure) i j = _
  rw [d.toTypeDDiagramLieIndex.coe_frobenius_apply,
    d.1.fieldOrder_eq_characteristic_pow]

/-- The minuscule-carrier Steinberg fixed group of an E₆ index is finite. -/
theorem TypeE6LieIndex.finite_fixedSubgroup_steinberg (d : TypeE6LieIndex) :
    Finite ↥(fixedSubgroup d.steinberg) := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.1.characteristic _
    d.steinberg d.1.fieldExponent 1 d.1.fieldExponent_pos.ne'
  intro g i j
  change (d.steinberg g : Matrix.GeneralLinearGroup (Fin 27) d.1.Closure) i j = _
  rw [d.coe_steinberg_apply, d.1.fieldOrder_eq_characteristic_pow]

/-- The minuscule-carrier Steinberg fixed group of an E₇ index is finite. -/
theorem TypeE7LieIndex.finite_fixedSubgroup_steinberg (d : TypeE7LieIndex) :
    Finite ↥(fixedSubgroup d.steinberg) := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.1.characteristic _
    d.steinberg d.1.fieldExponent 1 d.1.fieldExponent_pos.ne'
  intro g i j
  change (d.steinberg g : Matrix.GeneralLinearGroup (Fin 56) d.1.Closure) i j = _
  rw [d.coe_steinberg_apply, d.1.fieldOrder_eq_characteristic_pow]

end TauCeti
