/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Evaluation lemmas for `ContinuousLinearEquiv.ulift`

Pointwise evaluation formulas for Mathlib's `ContinuousLinearEquiv.ulift : ULift M ≃L[R] M` and
its inverse, complementing its definition over an arbitrary semiring `R`.
-/

public section
namespace ContinuousLinearEquiv
universe u v
variable {R : Type*} {M : Type u} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- `ContinuousLinearEquiv.ulift` maps a lifted element to its underlying value. -/
@[simp] theorem ulift_apply (x : ULift.{v} M) :
    (ContinuousLinearEquiv.ulift : ULift.{v} M ≃L[R] M) x = x.down := (rfl)
/-- The inverse of `ContinuousLinearEquiv.ulift` lifts an element via `ULift.up`. -/
@[simp] theorem ulift_symm_apply (x : M) :
    (ContinuousLinearEquiv.ulift : ULift.{v} M ≃L[R] M).symm x = ULift.up x := (rfl)

end ContinuousLinearEquiv
