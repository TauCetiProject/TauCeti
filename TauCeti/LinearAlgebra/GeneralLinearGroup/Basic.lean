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
* `LinearMap.GeneralLinearGroup.generalLinearEquiv_ofLinearEquiv` and
  `LinearMap.GeneralLinearGroup.generalLinearEquiv_symm_apply`: `generalLinearEquiv` and
  `ofLinearEquiv` are inverses.
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

/-- `generalLinearEquiv` sends `ofLinearEquiv f` back to `f`. -/
@[simp]
theorem generalLinearEquiv_ofLinearEquiv (f : M ≃ₗ[R] M) :
    generalLinearEquiv R M (ofLinearEquiv f) = f :=
  LinearEquiv.ext fun x ↦ by simp

/-- The inverse of `generalLinearEquiv` sends a linear equivalence to `ofLinearEquiv`. -/
@[simp]
theorem generalLinearEquiv_symm_apply (f : M ≃ₗ[R] M) :
    (generalLinearEquiv R M).symm f = ofLinearEquiv f :=
  (generalLinearEquiv R M).symm_apply_eq.mpr (generalLinearEquiv_ofLinearEquiv f).symm

end LinearMap.GeneralLinearGroup
