/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Basic facts about continuous linear maps

A vector lies in the kernel of `c • 1 - f`, for a continuous linear endomorphism `f` and a scalar
`c`, exactly when `f` multiplies it by `c`
(`ContinuousLinearMap.smul_one_sub_apply_eq_zero_iff`).
-/

public section

namespace ContinuousLinearMap

variable {R S M : Type*} [Ring R] [Monoid S] [TopologicalSpace M] [AddCommGroup M]
  [Module R M] [IsTopologicalAddGroup M] [DistribMulAction S M] [SMulCommClass R S M]
  [ContinuousConstSMul S M]

/-- A vector lies in the kernel of `c • 1 - f` exactly when `f` multiplies it by `c`. -/
theorem smul_one_sub_apply_eq_zero_iff {c : S} {f : M →L[R] M} {v : M} :
    (c • (1 : M →L[R] M) - f) v = 0 ↔ f v = c • v := by
  rw [sub_apply, sub_eq_zero, eq_comm, smul_apply, one_apply_eq_self]

end ContinuousLinearMap
