/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# The adjugate of a unitary matrix

For a unitary matrix the conjugate transpose is the inverse, and the adjugate is the determinant
times the inverse, so the adjugate is the determinant times the conjugate transpose. For a special
unitary matrix the two agree. This turns `star` on `Matrix.specialUnitaryGroup n α` into a
polynomial expression in the entries, which is what makes the small special unitary groups
computable by hand.

## Main results

* `Matrix.adjugate_eq_det_smul_star_of_mem_unitaryGroup`: the adjugate of a unitary matrix is its
  determinant times its conjugate transpose.
* `Matrix.specialUnitaryGroup.star_eq_adjugate`: the conjugate transpose of a special
  unitary matrix is its adjugate.
-/

public section

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n] {α : Type*} [CommRing α] [StarRing α]

/-- The adjugate of a unitary matrix is its determinant times its conjugate transpose: the
conjugate transpose is the inverse, and the adjugate is the determinant times the inverse. -/
theorem _root_.Matrix.adjugate_eq_det_smul_star_of_mem_unitaryGroup {A : Matrix n n α}
    (hA : A ∈ Matrix.unitaryGroup n α) : A.adjugate = A.det • star A := by
  calc A.adjugate = A.adjugate * (A * star A) := by
        rw [Matrix.mem_unitaryGroup_iff.mp hA, Matrix.mul_one]
    _ = A.det • star A := by
        rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

/-- The conjugate transpose of a special unitary matrix is its adjugate: it is the inverse, and
for determinant one the inverse is the adjugate. -/
theorem _root_.Matrix.specialUnitaryGroup.star_eq_adjugate (g : Matrix.specialUnitaryGroup n α) :
    star (g : Matrix n n α) = (g : Matrix n n α).adjugate := by
  have hmem := Matrix.mem_specialUnitaryGroup_iff.mp g.2
  rw [Matrix.adjugate_eq_det_smul_star_of_mem_unitaryGroup hmem.1, hmem.2, one_smul]

end TauCeti
