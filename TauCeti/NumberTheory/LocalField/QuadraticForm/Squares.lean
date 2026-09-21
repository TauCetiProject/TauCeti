/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.PowMonoidHom
public import TauCeti.NumberTheory.LocalField.Squares

/-!
# The local square interface for quadratic forms

This file records the local square theorem in the vocabulary used by the quadratic-form
invariants. The valuation, unit filtration, and sharpness theorem are owned by the local-field
arithmetic development; this module only names `v_K(2)` as `dyadicLevel` and changes the
codomain from the range of the squaring homomorphism to Mathlib's `Subgroup.square`.

The resulting statements are the square-class input for the quadratic defect and local Hilbert
symbol. In particular, the depth `2 * dyadicLevel K + 1` consists of squares, while the preceding
depth does not.

The mathematical convention follows O'Meara, *Introduction to Quadratic Forms*, §63A. No local
square argument is reproduced here.
-/

public section

open IsNonarchimedeanLocalField ValuativeRel

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The dyadic level `v_K(2)`, expressed using the supplied natural-valued valuation. -/
noncomputable def dyadicLevel (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Invertible (2 : K)] : ℕ :=
  natCastValuation K 2 (by simpa using (isUnit_of_invertible (2 : K)).ne_zero)

/-- Deep units are squares at the sharp local-field depth. -/
theorem unitFiltration_le_square [Invertible (2 : K)] :
    unitFiltration K (2 * dyadicLevel K + 1) ≤ Subgroup.square Kˣ := by
  rw [square_eq_powMonoidHom_two_range]
  simpa [dyadicLevel] using
    (unitFiltration_le_range_powMonoidHom_two (K := K)
      (by simpa using (isUnit_of_invertible (2 : K)).ne_zero))

/-- The sharp depth cannot be decreased: units at `2 * v_K(2)` are not all squares. -/
theorem not_unitFiltration_le_square [Invertible (2 : K)] :
    ¬ (unitFiltration K (2 * dyadicLevel K) ≤ Subgroup.square Kˣ) := by
  rw [square_eq_powMonoidHom_two_range]
  simpa [dyadicLevel] using
    (not_unitFiltration_le_range_powMonoidHom_two (K := K)
      (by simpa using (isUnit_of_invertible (2 : K)).ne_zero))

end TauCeti
