/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Coevaluation
public import Mathlib.LinearAlgebra.Trace

/-!
# The trace as a closed loop of coevaluation and contraction

For a finite-dimensional vector space `V` over a field `K`, Mathlib's `coevaluation K V` sends
`1` to the canonical tensor `∑ i, bᵢ ⊗ bᵢ*` of `V ⊗ V*`, and `contractLeft K V` contracts
`V* ⊗ V` to `K`. Inserting an endomorphism `f` on the `V` factor, swapping the two factors and
contracting gives `∑ i, bᵢ* (f bᵢ)`, which is the trace of `f`.

This is the linear-algebra content of the statement that in the rigid symmetric category of
finite-dimensional vector spaces the categorical trace of `f` is its linear trace.

## Main results

* `LinearMap.trace_eq_contractLeft_comm_rTensor_coevaluation`: the trace of `f` is the
  contraction of the swapped image of the coevaluation under `f ⊗ id`.
-/

public section

open Module TensorProduct

namespace LinearMap

variable (K : Type*) [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The trace of an endomorphism `f` of a finite-dimensional vector space is the contraction of
the canonical tensor `coevaluation K V 1` after applying `f` to its `V` factor and swapping the
two factors. -/
theorem trace_eq_contractLeft_comm_rTensor_coevaluation (f : V →ₗ[K] V) :
    trace K V f = contractLeft K V
      (TensorProduct.comm K V (Dual K V) (f.rTensor (Dual K V) (coevaluation K V 1))) := by
  classical
  rw [coevaluation_apply_one, trace_eq_matrix_trace K (Basis.ofVectorSpace K V), Matrix.trace]
  simp [toMatrix_apply, map_sum]

end LinearMap
