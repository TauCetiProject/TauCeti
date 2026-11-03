/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic

/-!
# Products of families of Lie algebras

Dependent products carry the coordinatewise Lie bracket. These products allow automorphisms
to permute isomorphic Lie algebra factors.
-/

public section

namespace Pi

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)]

instance instLieRing : LieRing (∀ i, L i) where
  bracket x y i := ⁅x i, y i⁆
  add_lie x y z := funext fun i => add_lie (x i) (y i) (z i)
  lie_add x y z := funext fun i => lie_add (x i) (y i) (z i)
  lie_self x := funext fun i => lie_self (x i)
  leibniz_lie x y z := funext fun i => leibniz_lie (x i) (y i) (z i)

/-- The product Lie bracket is evaluated coordinatewise. -/
@[simp]
theorem lie_apply (x y : ∀ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ := (rfl)

variable {R : Type*} [CommRing R] [∀ i, LieAlgebra R (L i)]

instance instLieAlgebra : LieAlgebra R (∀ i, L i) where
  lie_smul t x y := funext fun i => lie_smul t (x i) (y i)

end Pi
