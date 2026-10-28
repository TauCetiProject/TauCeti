/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basic

/-!
# Products of families of Lie algebras

A dependent product of Lie algebras has the coordinatewise bracket. No finiteness assumption
on the index is needed. This supplies the Lie algebra structure on finite products used to
compare adjoint centralizers and regular elements factor by factor.

The construction follows the binary product in `Mathlib.Algebra.Lie.Prod`.
-/

public section

namespace LieAlgebra.Pi

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)]

/-- The coordinatewise Lie ring structure on a dependent product. -/
instance instLieRing : LieRing (∀ i, L i) where
  bracket x y i := ⁅x i, y i⁆
  add_lie x y z := funext fun i ↦ add_lie (x i) (y i) (z i)
  lie_add x y z := funext fun i ↦ lie_add (x i) (y i) (z i)
  lie_self x := funext fun i ↦ lie_self (x i)
  leibniz_lie x y z := funext fun i ↦ leibniz_lie (x i) (y i) (z i)

/-- The bracket of two elements of a product is computed coordinatewise. -/
@[simp]
theorem bracket_apply (x y : ∀ i, L i) (i : ι) : ⁅x, y⁆ i = ⁅x i, y i⁆ := (rfl)

variable {R : Type*} [CommRing R] [∀ i, LieAlgebra R (L i)]

/-- The coordinatewise Lie algebra structure on a dependent product. -/
instance instLieAlgebra : LieAlgebra R (∀ i, L i) where
  lie_smul r x y := funext fun i ↦ lie_smul r (x i) (y i)

end LieAlgebra.Pi
