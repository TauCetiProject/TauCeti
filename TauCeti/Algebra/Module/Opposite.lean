/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Tower

/-!
# Inverse right multiplication on modules

For an `R`-algebra `A`, a module over `Aᵐᵒᵖ` is a right `A`-module. Inverse right
multiplication gives a homomorphism from `Aˣ` to its `R`-linear endomorphisms. This turns
the right action into a left action of units, as used in balanced tensor constructions.
-/

public section

namespace TauCeti

open MulOpposite

variable (R A M : Type*) [CommSemiring R] [Semiring A] [Algebra R A]
  [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]

/-- Units of an algebra act on a right module by inverse right multiplication. -/
def inverseRightAction : Aˣ →* Module.End R M where
  toFun d := Algebra.lsmul R R M (op (↑d⁻¹ : A))
  map_one' := by ext m; simp
  map_mul' d e := by
    ext m
    simp only [mul_inv_rev, Units.val_mul, Algebra.lsmul_apply,
      mul_apply_eq_comp, op_mul, mul_smul]

/-- The left action of a unit is right multiplication by its inverse. -/
@[simp]
theorem inverseRightAction_apply (d : Aˣ) (m : M) :
    inverseRightAction R A M d m = op (↑d⁻¹ : A) • m := (rfl)

end TauCeti
