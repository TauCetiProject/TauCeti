/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Kronecker products of invertible matrices

The Kronecker product gives the homomorphism from a product of general linear groups to the
one indexed by pairs. It expresses the action on a tensor product in product-basis coordinates.
-/

public section

open scoped Kronecker

namespace Matrix.GeneralLinearGroup

variable {R m n : Type*} [CommSemiring R] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

/-- The Kronecker product of two invertible matrices, as a group homomorphism. -/
def kroneckerHom : GL m R × GL n R →* GL (m × n) R :=
  { toFun := fun g ↦ g.1.kronecker g.2
    map_one' := Units.ext one_kronecker_one
    map_mul' := fun g h ↦ Units.ext <|
      mul_kronecker_mul (g.1 : Matrix m m R) (h.1 : Matrix m m R)
        (g.2 : Matrix n n R) (h.2 : Matrix n n R) }

/-- The underlying matrix of `kroneckerHom` is the Kronecker product of the underlying matrices. -/
@[simp]
theorem coe_kroneckerHom (g : GL m R × GL n R) :
    (kroneckerHom g : Matrix (m × n) (m × n) R) =
      (g.1 : Matrix m m R) ⊗ₖ (g.2 : Matrix n n R) := (rfl)

end Matrix.GeneralLinearGroup
