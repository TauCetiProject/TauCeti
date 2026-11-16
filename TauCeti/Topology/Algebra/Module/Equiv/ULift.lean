/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Universe-lifting continuous linear equivalence lemmas

This file provides `@[simp]` evaluation and coercion lemmas for Mathlib's universe-lifting
continuous linear equivalence `ContinuousLinearEquiv.ulift : ULift.{w} M ≃L[R] M`.
-/

public section

namespace ContinuousLinearEquiv

universe u v w

variable {R : Type u} {M : Type v} [Semiring R] [AddCommMonoid M] [Module R M]
  [TopologicalSpace M]

/-- `ContinuousLinearEquiv.ulift` extracts the underlying element with `ULift.down`. -/
@[simp] theorem ulift_apply (x : ULift.{w} M) :
    (ContinuousLinearEquiv.ulift : ULift.{w} M ≃L[R] M) x = x.down := (rfl)

/-- The inverse of `ContinuousLinearEquiv.ulift` lifts an element with `ULift.up`. -/
@[simp] theorem ulift_symm_apply (x : M) :
    (ContinuousLinearEquiv.ulift : ULift.{w} M ≃L[R] M).symm x = ULift.up x := (rfl)

/-- The underlying linear equivalence of `ContinuousLinearEquiv.ulift` is `ULift.moduleEquiv`. -/
theorem toLinearEquiv_ulift :
    (ContinuousLinearEquiv.ulift : ULift.{w} M ≃L[R] M).toLinearEquiv = ULift.moduleEquiv := (rfl)

end ContinuousLinearEquiv
