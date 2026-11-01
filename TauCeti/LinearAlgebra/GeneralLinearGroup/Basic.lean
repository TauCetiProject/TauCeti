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

end LinearMap.GeneralLinearGroup
