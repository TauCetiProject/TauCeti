/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Opposite
public import Mathlib.Algebra.Algebra.Tower

/-!
# Modules over opposite algebras

For an `R`-algebra `A`, a module over `Aᵐᵒᵖ` is a right `A`-module. Inverse right
multiplication gives a homomorphism from `Aˣ` to its `R`-linear endomorphisms. This turns
the right action into a left action of units, as used in balanced tensor constructions.

A left `A`-module is also a module over the double opposite `Aᵐᵒᵖᵐᵒᵖ`, by `TauCeti.opOpModule`. This
is the form in which results about right modules, applied with `Aᵐᵒᵖ` in place of `A`, reach left
`A`-modules. It is not a global instance, and `TauCeti.opOpSemilinearEquiv` transports module
properties along the identity map.
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

section OpOp

/-- A left `A`-module, seen as a module over the double opposite `Aᵐᵒᵖᵐᵒᵖ`. -/
abbrev opOpModule (A N : Type*) [Semiring A] [AddCommMonoid N] [Module A N] : Module Aᵐᵒᵖᵐᵒᵖ N :=
  Module.compHom N (RingEquiv.opOp A).symm.toRingHom

attribute [local instance] opOpModule RingHomInvPair.of_ringEquiv

/-- The action of `Aᵐᵒᵖᵐᵒᵖ` on a left `A`-module is compatible with the action of the base. -/
theorem isScalarTower_opOpModule {R A N : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
    [AddCommMonoid N] [Module R N] [Module A N] [IsScalarTower R A N] :
    IsScalarTower R Aᵐᵒᵖᵐᵒᵖ N :=
  IsScalarTower.of_algebraMap_smul fun r x => algebraMap_smul A r x

/-- A left `A`-module is semilinearly identified with itself over the double opposite `Aᵐᵒᵖᵐᵒᵖ`. -/
def opOpSemilinearEquiv {A N : Type*} [Semiring A] [AddCommMonoid N] [Module A N] :
    N ≃ₛₗ[RingHomClass.toRingHom (RingEquiv.opOp A)] N :=
  { Equiv.refl N with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
theorem opOpSemilinearEquiv_apply {A N : Type*} [Semiring A] [AddCommMonoid N] [Module A N]
    (x : N) : opOpSemilinearEquiv (A := A) x = x :=
  (rfl)

@[simp]
theorem opOpSemilinearEquiv_symm_apply {A N : Type*} [Semiring A] [AddCommMonoid N] [Module A N]
    (x : N) : (opOpSemilinearEquiv (A := A)).symm x = x :=
  (rfl)

end OpOp

end TauCeti
