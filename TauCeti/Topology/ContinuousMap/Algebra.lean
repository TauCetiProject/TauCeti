/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# The kernel of evaluation on continuous maps

Mathlib's `ContinuousMap.evalCLM R x` is evaluation at a point `x` on the continuous maps
`C(α, M)` into a topological `R`-module `M`, as a continuous `R`-linear map. Its kernel is the
submodule of continuous maps vanishing at `x`; this module records the pointwise form of
membership in that kernel.

## Main results

* `TauCeti.ContinuousMap.coe_apply_eq_zero_of_mem_ker_evalCLM`: a continuous map in the kernel of
  evaluation at a point vanishes there, stated with the evaluation written as a function value.
-/

public section

namespace TauCeti

variable (R : Type*) [Semiring R]
variable (M : Type*) [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M] [Module R M]
  [ContinuousConstSMul R M]

/-- A continuous map in the kernel of evaluation at a point vanishes there. -/
theorem ContinuousMap.coe_apply_eq_zero_of_mem_ker_evalCLM {α : Type*} [TopologicalSpace α]
    (x : α) (f : (ContinuousMap.evalCLM R x : C(α, M) →L[R] M).ker) : (f : C(α, M)) x = 0 :=
  (ContinuousMap.evalCLM_apply R x (f : C(α, M))).symm.trans (LinearMap.mem_ker.mp f.2)

end TauCeti
