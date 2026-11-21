/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.Discriminant

/-!
# Discriminants of two bases differ by a unit square

Let `B` be an algebra over a commutative ring `A` with two finite bases `b` and `b'`. The
change-of-basis matrix `P` between them is invertible, so its determinant is a unit of `A`, and
`Algebra.discr_of_matrix_vecMul` gives `discr A b' = (det P) ^ 2 * discr A b`. Thus the
discriminant of a basis is well defined up to the square of a unit of `A`. Over a field this is
what makes the square class of the discriminant of a finite separable extension independent of
the basis; over a ring of integers it is the statement that the discriminants of two integral
bases differ by the square of an integral unit.

## Main results

* `Module.Basis.exists_discr_eq_sq_mul_discr`: `discr A b' = u ^ 2 * discr A b` for some unit
  `u` of `A`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §2.
-/

public section

namespace Module.Basis

variable {A B ι ι' : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι']

/-- **The discriminants of two bases differ by a unit square.** For two finite bases `b` and `b'`
of an `A`-algebra `B`, `discr A b' = u ^ 2 * discr A b` for some unit `u` of `A`, namely the
determinant of the change-of-basis matrix. -/
theorem exists_discr_eq_sq_mul_discr (b : Basis ι A B) (b' : Basis ι' A B) :
    ∃ u : Aˣ, Algebra.discr A b' = (u : A) ^ 2 * Algebra.discr A b := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨1, Subsingleton.elim _ _⟩
  -- Reindex `b` by `ι'`, so that the change-of-basis matrix to `b'` is square.
  set c := b.reindex (b.indexEquiv b')
  have hunit : IsUnit (c.toMatrix b').det := by
    rw [← LinearMap.toMatrix_id_eq_basis_toMatrix b' c]
    exact LinearEquiv.isUnit_det (LinearEquiv.refl A B) b' c
  refine ⟨hunit.unit, ?_⟩
  conv_lhs => rw [← c.toMatrix_map_vecMul b']
  rw [IsUnit.unit_spec, Algebra.discr_of_matrix_vecMul, Basis.coe_reindex, Algebra.discr_reindex]

end Module.Basis
