/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Defs

/-!
# The trace along a tower of scalars

Let `A` be a commutative `R`-algebra that is free of finite rank as an `R`-module, and let `M` be
a free `A`-module of finite rank. An `A`-linear endomorphism `f` of `M` has a trace over `A`, and,
viewed as an `R`-linear endomorphism, a trace over `R`. The second is the algebra trace from `A`
to `R` of the first. This is the module version of the transitivity of the algebra trace
`Algebra.trace_trace_of_basis`, and the additive counterpart of `LinearMap.det_restrictScalars`.

## Main results

* `LinearMap.trace_restrictScalars`: `tr_R(f) = Tr_{A/R}(tr_A(f))`.
-/

public section

namespace LinearMap

open Module

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
  [Module.Finite R A] [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
  [Module.Free A M] [Module.Finite A M]

/-- **The trace along a tower of scalars.** For a free `A`-module `M` of finite rank, where `A` is
a free `R`-algebra of finite rank, the `R`-trace of an `A`-linear endomorphism is the algebra trace
of its `A`-trace. -/
theorem trace_restrictScalars (f : M →ₗ[A] M) :
    trace R M (f.restrictScalars R) = Algebra.trace R A (trace A M f) := by
  classical
  let bA := Free.chooseBasis R A
  let bM := Free.chooseBasis A M
  rw [trace_eq_matrix_trace R (bA.smulTower' bM), restrictScalars_toMatrix,
    trace_eq_matrix_trace A bM, Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type]
  simp [Algebra.trace_eq_matrix_trace bA, Matrix.trace]

end LinearMap
