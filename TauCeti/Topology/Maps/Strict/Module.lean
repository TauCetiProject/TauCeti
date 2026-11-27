/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Strict.Module

/-!
# Evaluation lemmas for strict linear maps

This file supplements `Mathlib.Topology.Maps.Strict.Module` with the `@[simp]` evaluation lemma
for `ContinuousLinearEquiv.quotKerEquivRange` on quotient classes.
-/

public section

namespace ContinuousLinearEquiv

variable {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [AddCommGroup N] [Module R N] [TopologicalSpace N]

/-- Applying `ContinuousLinearEquiv.quotKerEquivRange` to `[x]` gives `f x`. -/
@[simp]
theorem coe_quotKerEquivRange_mk {f : M →ₗ[R] N} (hf : Topology.IsStrictMap f) (x : M) :
    ((ContinuousLinearEquiv.quotKerEquivRange hf (Submodule.Quotient.mk x) :
      LinearMap.range f) : N) = f x :=
  LinearMap.quotKerEquivRange_apply_mk f x

end ContinuousLinearEquiv
