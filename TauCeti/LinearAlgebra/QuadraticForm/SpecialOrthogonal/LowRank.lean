/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic
public import TauCeti.LinearAlgebra.Determinant

/-!
# Special orthogonal groups in rank at most one

A determinant-one automorphism of a finite free module of rank at most one over a commutative
ring is the identity. Thus its special orthogonal group is trivial, even for a degenerate
quadratic form and in characteristic two. This supplies the low-dimensional boundary of
spinor-norm image calculations.
-/

public section

namespace QuadraticMap

open TauCeti.QuadraticMap

variable {R V N : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [Module.Free R V] [Module.Finite R V] [AddCommMonoid N] [Module R N]

/-- The special orthogonal group of a quadratic map on a finite free module of rank at most
one is trivial.
No nondegeneracy or characteristic assumption is needed. -/
@[simp]
theorem specialOrthogonalGroup_eq_bot_of_finrank_le_one (Q : QuadraticMap R V N)
    (hV : Module.finrank R V ≤ 1) : specialOrthogonalGroup Q = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun g hg => ?_
  exact (Subgroup.eq_bot_iff_forall _).mp
    (LinearEquiv.det_ker_eq_bot_of_finrank_le_one hV) g
    (mem_specialOrthogonalGroup_iff.mp hg).2

end QuadraticMap
