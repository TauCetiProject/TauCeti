/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# Lemmas for continuous linear equivalences on submodules

This file supplements `Mathlib.Topology.Algebra.Module.Equiv.Submodule` with `@[simp]` evaluation
lemmas for `Submodule.topContEquiv` and `ContinuousLinearEquiv.ofEq`.
-/

public section

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]

namespace Submodule

/-- Applying `Submodule.topContEquiv` returns the underlying element of `M`. -/
@[simp]
theorem topContEquiv_apply (x : (⊤ : Submodule R M)) :
    (Submodule.topContEquiv x : M) = (x : M) :=
  rfl

end Submodule

namespace ContinuousLinearEquiv

/-- Applying `ContinuousLinearEquiv.ofEq` preserves the underlying element of `M`. -/
@[simp]
theorem coe_ofEq_apply {p q : Submodule R M} (h : p = q) (x : p) :
    ((ContinuousLinearEquiv.ofEq p q h x : q) : M) = (x : M) :=
  rfl

end ContinuousLinearEquiv
