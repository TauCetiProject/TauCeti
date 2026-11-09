/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Defs

import TauCeti.LinearAlgebra.Trace.Basic

/-!
# The trace along a tower of scalars

Let `A` be a commutative `R`-algebra that is free as an `R`-module, and let `M` be a free
`A`-module. An `A`-linear endomorphism `f` of `M` has a trace over `A`, and, viewed as an
`R`-linear endomorphism, a trace over `R`. The second is the algebra trace from `A` to `R` of the
first. This is the module version of the transitivity of the algebra trace
`Algebra.trace_trace_of_basis`, and the additive counterpart of `LinearMap.det_restrictScalars`.

## Main results

* `LinearMap.trace_restrictScalars`: `tr_R(f) = Tr_{A/R}(tr_A(f))`.
-/

public section

namespace LinearMap

open Module

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Free A M]

/-- **The trace along a tower of scalars.** For a free `A`-module `M`, where `A` is a free
`R`-algebra, the `R`-trace of an `A`-linear endomorphism is the algebra trace of its `A`-trace. -/
theorem trace_restrictScalars (f : M →ₗ[A] M) :
    trace R M (f.restrictScalars R) = Algebra.trace R A (trace A M f) := by
  classical
  nontriviality R
  nontriviality M using Subsingleton.elim f 0
  have := Module.nontrivial A M
  obtain ⟨ιA, bA⟩ := Free.exists_basis (R := R) (M := A)
  obtain ⟨ιM, bM⟩ := Free.exists_basis (R := A) (M := M)
  have := bA.index_nonempty
  have := bM.index_nonempty
  cases fintypeOrInfinite ιA; swap
  · simp [Algebra.trace_eq_zero_of_not_exists_basis R
      fun ⟨_, ⟨b⟩⟩ ↦ not_finite_of_infinite_basis bA (.of_basis b),
      TauCeti.LinearMap.trace_eq_zero_of_not_finite
        (not_finite_of_infinite_basis (bA.smulTower bM))]
  cases fintypeOrInfinite ιM; swap
  · simp [TauCeti.LinearMap.trace_eq_zero_of_not_finite (not_finite_of_infinite_basis bM),
      TauCeti.LinearMap.trace_eq_zero_of_not_finite
        (not_finite_of_infinite_basis (bA.smulTower bM))]
  rw [trace_eq_matrix_trace R (bA.smulTower' bM), restrictScalars_toMatrix,
    trace_eq_matrix_trace A bM, Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type]
  simp [Algebra.trace_eq_matrix_trace bA, Matrix.trace]

end LinearMap
