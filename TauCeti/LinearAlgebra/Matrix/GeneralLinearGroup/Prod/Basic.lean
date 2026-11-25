/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Invertible matrices over a product of semirings

A matrix over a product semiring `A × B` is a pair of matrices of the same size, one over `A` and
one over `B`, and it is invertible exactly when both are. So `GL n (A × B) ≃* GL n A × GL n B`
(`TauCeti.prodGL`). The semirings may be noncommutative.

## Main definitions

* `TauCeti.prodGL`: the isomorphism `GL n (A × B) ≃* GL n A × GL n B` for arbitrary semirings,
  taking components entrywise. Mathlib's `Matrix.GeneralLinearGroup.prodEquiv` is the same
  isomorphism for commutative rings.

## Main results

* `TauCeti.prodGL_apply_fst`, `TauCeti.prodGL_apply_snd`: the components of `TauCeti.prodGL` are
  entrywise application of the two projections.
* `TauCeti.unitsMap_fst_prodGL_symm`, `TauCeti.unitsMap_snd_prodGL_symm`: the projections recover
  the two components from the inverse.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

section prodGL

variable (n : Type*) [Fintype n] [DecidableEq n] (A B : Type*) [Semiring A] [Semiring B]

/-- The isomorphism `GL n (A × B) ≃* GL n A × GL n B` taking the two components of every entry,
for arbitrary (possibly noncommutative) semirings: Mathlib's `Matrix.prodRingEquiv` on units.
Mathlib's `Matrix.GeneralLinearGroup.prodEquiv` is the same isomorphism for commutative
rings. -/
def prodGL : GL n (A × B) ≃* GL n A × GL n B :=
  (Units.mapEquiv (Matrix.prodRingEquiv n A B).toMulEquiv).trans MulEquiv.prodUnits

variable {n A B}

/-- The first component of `prodGL` is entrywise application of the first projection. -/
@[simp]
theorem prodGL_apply_fst (g : GL n (A × B)) :
    (prodGL n A B g).1 = Units.map ((RingHom.fst A B).mapMatrix (m := n)) g :=
  (rfl)

/-- The second component of `prodGL` is entrywise application of the second projection. -/
@[simp]
theorem prodGL_apply_snd (g : GL n (A × B)) :
    (prodGL n A B g).2 = Units.map ((RingHom.snd A B).mapMatrix (m := n)) g :=
  (rfl)

/-- The entries of the invertible matrix over `A × B` with components `g.1` and `g.2` are the
pairs of corresponding entries. -/
@[simp]
theorem coe_prodGL_symm_apply (g : GL n A × GL n B) (i j : n) :
    ((prodGL n A B).symm g : Matrix n n (A × B)) i j =
      ((g.1 : Matrix n n A) i j, (g.2 : Matrix n n B) i j) :=
  (rfl)

/-- Applying the first projection entrywise to the invertible matrix over `A × B` with
components `g.1` and `g.2` recovers `g.1`. -/
@[simp]
theorem unitsMap_fst_prodGL_symm (g : GL n A × GL n B) :
    Units.map ((RingHom.fst A B).mapMatrix (m := n)) ((prodGL n A B).symm g) = g.1 := by
  rw [← prodGL_apply_fst, MulEquiv.apply_symm_apply]

/-- Applying the second projection entrywise to the invertible matrix over `A × B` with
components `g.1` and `g.2` recovers `g.2`. -/
@[simp]
theorem unitsMap_snd_prodGL_symm (g : GL n A × GL n B) :
    Units.map ((RingHom.snd A B).mapMatrix (m := n)) ((prodGL n A B).symm g) = g.2 := by
  rw [← prodGL_apply_snd, MulEquiv.apply_symm_apply]

end prodGL

end TauCeti
