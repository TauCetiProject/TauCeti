/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic

/-!
# The adjugate of a special unitary matrix

For a unitary matrix the conjugate transpose is a right inverse, so the adjugate is the
determinant times the conjugate transpose (`Matrix.adjugate_eq_det_smul_of_mul_eq_one`). For a
special unitary matrix the two agree. This turns `star` on `Matrix.specialUnitaryGroup n α` into a
polynomial expression in the entries, which is what makes the small special unitary groups
computable by hand.

## Main results

* `Matrix.specialUnitaryGroup.star_eq_adjugate`: the conjugate transpose of a special
  unitary matrix is its adjugate.
-/

public section

namespace Matrix.specialUnitaryGroup

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [CommRing α] [StarRing α]

/-- The conjugate transpose of a special unitary matrix is its adjugate: it is the inverse, and
for determinant one the inverse is the adjugate. -/
theorem star_eq_adjugate (g : specialUnitaryGroup n α) :
    star (g : Matrix n n α) = (g : Matrix n n α).adjugate := by
  obtain ⟨hU, hdet⟩ := mem_specialUnitaryGroup_iff.mp g.2
  rw [adjugate_eq_det_smul_of_mul_eq_one (mem_unitaryGroup_iff.mp hU), hdet, one_smul]

end Matrix.specialUnitaryGroup
