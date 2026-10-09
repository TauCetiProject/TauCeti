/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup.Finiteness
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeB.Basic
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Basic

/-!
# Finiteness of the type-B and type-C Steinberg fixed groups

The Steinberg maps for the ordinary type-B and type-C families act on every matrix entry by
the field-order Frobenius. The positive field exponent recorded by each validated index
therefore places the fixed points in finitely many finite-field coordinates.
-/

public section

namespace TauCeti

/-- The type-B Steinberg fixed group is finite, using the Frobenius coordinates of the
spin carrier. -/
theorem TypeBLieIndex.finite_fixedPoints (d : TypeBLieIndex) : Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.1.characteristic _
    d.steinberg d.1.fieldExponent 1 d.1.fieldExponent_pos.ne'
  intro g i j
  change (d.steinberg g : Matrix.GeneralLinearGroup
    (Fin (TypeBSpinCarrier.dimension d.carrierRank)) d.1.Closure) i j = _
  rw [d.steinberg_def, d.coe_frobenius_apply, d.1.fieldOrder_eq_characteristic_pow]

/-- The type-C Steinberg fixed group is finite, using the Frobenius coordinates of the
standard symplectic carrier. -/
theorem TypeCLieIndex.finite_fixedPoints (d : TypeCLieIndex) : Finite d.FixedPoints := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.1.characteristic _
    d.steinberg d.1.fieldExponent 1 d.1.fieldExponent_pos.ne'
  intro g i j
  change (d.steinberg g : Matrix.GeneralLinearGroup
    (Fin (d.carrierRank + 1 + (d.carrierRank + 1))) d.1.Closure) i j = _
  rw [d.steinberg_def, d.coe_frobenius_apply, d.1.fieldOrder_eq_characteristic_pow]

end TauCeti
