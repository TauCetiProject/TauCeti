/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Algebra.DualNumber

/-!
# Scalar compatibility for dual numbers

The coordinatewise scalar action on dual numbers commutes with multiplication. These
instances make bilinear multiplication and convolution available with that module structure.
-/

public section

namespace TauCeti

variable {R B : Type*} [CommSemiring R] [Semiring B] [Algebra R B]

/-- Coordinatewise scalar multiplication associates with multiplication of dual numbers. -/
instance dualNumberIsScalarTower : IsScalarTower R (DualNumber B) (DualNumber B) where
  smul_assoc r x y := by
    ext <;> simp [smul_eq_mul, smul_add]

/-- Coordinatewise scalar multiplication commutes with left multiplication of dual numbers. -/
instance dualNumberSMulCommClass : SMulCommClass R (DualNumber B) (DualNumber B) where
  smul_comm r x y := by
    ext <;> simp [smul_eq_mul, smul_add]

end TauCeti
