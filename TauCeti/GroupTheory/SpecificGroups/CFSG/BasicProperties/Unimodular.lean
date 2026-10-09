/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FixedSubgroup.Finiteness
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Unimodular

/-!
# Finiteness of the unimodular exceptional fixed groups

The Geck Frobenius of every valid Lie-type index has finitely many fixed points: it acts on
every matrix entry by the field-order power, and the recorded field exponent is positive.
The finite-coordinate criterion therefore applies with iterate one.

For the untwisted families `E₈(q)`, `F₄(q)` and `G₂(q)`, the family Steinberg map is this
Frobenius on the same carrier. Thus their exact family fixed subgroups are finite.
-/

public section

namespace TauCeti

/-- The field-order Frobenius on the Geck carrier has finitely many fixed points, for every
valid Lie-type index. -/
theorem ValidLieTypeIndex.finite_fixedSubgroup_geckFrobenius (d : ValidLieTypeIndex) :
    Finite ↥(fixedSubgroup d.geckFrobenius) := by
  apply finite_fixedSubgroup_of_frobenius_matrix_subgroup d.characteristic d.geckPoints
    d.geckFrobenius d.fieldExponent 1 d.fieldExponent_pos.ne'
  intro g i j
  change ((d.geckFrobenius g : Matrix.GeneralLinearGroup _ d.Closure) i j) = _
  rw [d.coe_geckFrobenius_apply, d.fieldOrder_eq_characteristic_pow]

/-- The Steinberg fixed groups of `E₈(q)`, `F₄(q)` and `G₂(q)` are finite. -/
theorem UnimodularExceptionalIndex.finite_fixedPoints (d : UnimodularExceptionalIndex) :
    Finite ↥(fixedSubgroup d.steinberg) := by
  rw [d.steinberg_eq_geckFrobenius]
  exact d.1.1.finite_fixedSubgroup_geckFrobenius

end TauCeti
