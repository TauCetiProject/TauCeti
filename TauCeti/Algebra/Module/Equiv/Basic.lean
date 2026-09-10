/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic

/-!
# Evaluating multiplication by a unit of the base ring

Mathlib's `LinearEquiv.smulOfUnit` packages multiplication by a unit `u` of the base ring as a
linear equivalence, but records no lemmas evaluating it at a vector. This file supplies those
evaluation lemmas, in the `simp`-normal forms that rewrite an application of
`LinearEquiv.smulOfUnit` to a scalar multiplication.

## Main results

* `LinearEquiv.smulOfUnit_apply`: `LinearEquiv.smulOfUnit u` acts as multiplication by `u`.
* `LinearEquiv.smulOfUnit_symm_apply`: its inverse acts as multiplication by `u⁻¹`.
-/

public section

namespace LinearEquiv

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Multiplication by a unit of the base ring, evaluated: `LinearEquiv.smulOfUnit u` sends `x` to
`u • x`. -/
@[simp]
theorem smulOfUnit_apply (u : Rˣ) (x : M) : (smulOfUnit u : M ≃ₗ[R] M) x = (u : R) • x :=
  (rfl)

/-- The inverse of multiplication by a unit `u`, evaluated at `x`, is multiplication by `u⁻¹`. -/
@[simp]
theorem smulOfUnit_symm_apply (u : Rˣ) (x : M) :
    (smulOfUnit u : M ≃ₗ[R] M).symm x = ((u⁻¹ : Rˣ) : R) • x :=
  (rfl)

end LinearEquiv
