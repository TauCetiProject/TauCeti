/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices over a product of semirings

An invertible matrix over a product `A × B` of semirings is the same as a pair of invertible
matrices over `A` and over `B`: its entrywise components. Mathlib's
`Matrix.GeneralLinearGroup.prodEquiv` states this only over commutative rings; here `A` and `B`
are arbitrary, possibly noncommutative, semirings.

## Main definitions

* `TauCeti.prodEquivGL`: the multiplicative equivalence `GL n (A × B) ≃* GL n A × GL n B`.

## Main results

* `TauCeti.prodEquivGL_apply_fst`, `TauCeti.prodEquivGL_apply_snd`: the two components of an
  invertible matrix over `A × B` are its images under the two projections.
* `TauCeti.coe_prodEquivGL_symm_apply`: the matrix over `A × B` with given components.
-/

public section

namespace TauCeti

variable (n : Type*) [Fintype n] [DecidableEq n] (A B : Type*) [Semiring A] [Semiring B]

/-- The equivalence between the invertible matrices over a product `A × B` of semirings and the
pairs of invertible matrices over `A` and over `B`, taking the entrywise components. -/
def prodEquivGL : GL n (A × B) ≃* GL n A × GL n B :=
  (Units.mapEquiv (Matrix.prodRingEquiv n A B).toMulEquiv).trans MulEquiv.prodUnits

variable {n A B}

/-- The first component of an invertible matrix over `A × B` is its image under the first
projection. -/
@[simp]
theorem prodEquivGL_apply_fst (w : GL n (A × B)) :
    (prodEquivGL n A B w).1 = Units.map (RingHom.fst A B).mapMatrix.toMonoidHom w :=
  (rfl)

/-- The second component of an invertible matrix over `A × B` is its image under the second
projection. -/
@[simp]
theorem prodEquivGL_apply_snd (w : GL n (A × B)) :
    (prodEquivGL n A B w).2 = Units.map (RingHom.snd A B).mapMatrix.toMonoidHom w :=
  (rfl)

/-- The invertible matrix over `A × B` with components `p.1` and `p.2` has the pairs of their
entries as entries. -/
@[simp]
theorem coe_prodEquivGL_symm_apply (p : GL n A × GL n B) :
    ((prodEquivGL n A B).symm p : Matrix n n (A × B)) =
      Matrix.of fun i j ↦ ((p.1 : Matrix n n A) i j, (p.2 : Matrix n n B) i j) :=
  (rfl)

end TauCeti
