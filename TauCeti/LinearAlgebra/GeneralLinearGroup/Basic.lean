/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Basic API for the general linear group

Supplements to `Mathlib.LinearAlgebra.GeneralLinearGroup.Basic`.

## Main statements

* `LinearMap.GeneralLinearGroup.val_ofLinearEquiv`: the endomorphism underlying
  `ofLinearEquiv f` is `f`.
* `LinearMap.GeneralLinearGroup.ofLinearEquiv_one`: `ofLinearEquiv` sends the identity equivalence
  to the identity.
* `Module.End.units_inv_apply_apply`, `Module.End.units_apply_inv_apply`: a unit of `Module.End R M`
  and its inverse undo each other on vectors.
-/

public section

namespace LinearMap.GeneralLinearGroup

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The endomorphism underlying the general-linear-group element of a linear equivalence is that
equivalence. Mathlib's `coe_ofLinearEquiv` records this only for the underlying function. -/
@[simp]
theorem val_ofLinearEquiv (f : M ≃ₗ[R] M) :
    ((ofLinearEquiv f : GeneralLinearGroup R M) : Module.End R M) = f.toLinearMap :=
  LinearMap.ext fun x ↦ congrFun (coe_ofLinearEquiv f) x

/-- The general-linear-group element of the identity equivalence is the identity. -/
@[simp]
theorem ofLinearEquiv_one : ofLinearEquiv (1 : M ≃ₗ[R] M) = (1 : GeneralLinearGroup R M) :=
  Units.ext (LinearMap.ext fun _ ↦ rfl)

end LinearMap.GeneralLinearGroup

namespace Module.End

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The inverse of a unit `a` of `Module.End R M` undoes `a`. -/
@[simp]
theorem units_inv_apply_apply (a : (Module.End R M)ˣ) (m : M) :
    (↑a⁻¹ : Module.End R M) ((a : Module.End R M) m) = m := by
  rw [← _root_.mul_apply_eq_comp, Units.inv_mul, _root_.one_apply_eq_self]

/-- A unit `a` of `Module.End R M` undoes its inverse. -/
@[simp]
theorem units_apply_inv_apply (a : (Module.End R M)ˣ) (m : M) :
    (a : Module.End R M) ((↑a⁻¹ : Module.End R M) m) = m := by
  rw [← _root_.mul_apply_eq_comp, Units.mul_inv, _root_.one_apply_eq_self]

end Module.End
