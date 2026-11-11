/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-!
# Traces of products alternating with a fixed matrix

Fix a matrix `S`. This file expands the quadratic map `M ↦ trace (M * S * M * S)` at a sum, so
that polarization recovers the symmetric bilinear map `(M, N) ↦ trace (M * S * N * S)` from it.
It also computes the trace of `2 P - 1`, which vanishes for a trace-one `2 × 2` matrix `P` such as
the orthogonal projector onto a line of `ℂ²`, and records that reindexing rows and columns along
one equivalence preserves the trace.

## Main results

* `Matrix.trace_add_mul_add_mul`: the expansion of `trace ((M + N) * S * (M + N) * S)` into the
  two pure terms and twice the mixed term.
* `Matrix.trace_two_mul_sub_one`: `trace (2 P - 1) = 2 trace P - n` for an `n × n` matrix `P`.
* `Matrix.trace_reindex_self`: reindexing rows and columns along one equivalence preserves the
  trace.
* `Matrix.map_trace_mul_comm`: a trace `τ` on a possibly noncommutative ring of entries gives the
  trace `τ ∘ Tr` on matrices.
-/

public section

namespace Matrix

variable {m n R : Type*} [Fintype m] [Fintype n] [CommSemiring R]

/-- The quadratic map `M ↦ trace (M * S * M * S)` expands at a sum into the two pure terms plus
twice the mixed term. The matrices may be rectangular. -/
theorem trace_add_mul_add_mul (M N : Matrix m n R) (S : Matrix n m R) :
    ((M + N) * S * (M + N) * S).trace =
      (M * S * M * S).trace + 2 * (M * S * N * S).trace + (N * S * N * S).trace := by
  have hcross : (N * S * M * S).trace = (M * S * N * S).trace := by
    simpa only [Matrix.mul_assoc] using trace_mul_comm (N * S) (M * S)
  simp only [Matrix.add_mul, Matrix.mul_add, trace_add, hcross]
  ring

/-- The trace of `2 P - 1` is `2 trace P - n` for an `n × n` matrix `P`. -/
theorem trace_two_mul_sub_one {R : Type*} [Ring R] [DecidableEq n] (P : Matrix n n R) :
    (2 * P - 1).trace = 2 * P.trace - Fintype.card n := by
  rw [two_mul, two_mul, trace_sub, trace_add, trace_one]

/-- Reindexing the rows and columns of a square matrix along the same equivalence preserves its
trace. -/
theorem trace_reindex_self {R : Type*} [AddCommMonoid R] (e : m ≃ n) (A : Matrix m m R) :
    (reindex e e A).trace = A.trace := by
  simpa [trace] using e.symm.sum_comp (fun i ↦ A i i)

/-- A trace `τ` on a possibly noncommutative ring of entries, `τ (x * y) = τ (y * x)`, gives a trace
`τ ∘ Tr` on matrices: `τ (Tr (M N)) = τ (Tr (N M))`. The matrices may be rectangular. -/
theorem map_trace_mul_comm {α β F : Type*} [NonUnitalNonAssocSemiring α] [AddCommMonoid β]
    [FunLike F α β] [AddMonoidHomClass F α β] (τ : F) (hτ : ∀ x y, τ (x * y) = τ (y * x))
    (A : Matrix m n α) (B : Matrix n m α) : τ (A * B).trace = τ (B * A).trace := by
  simp only [trace, diag_apply, Matrix.mul_apply, map_sum, hτ (A _ _)]
  exact Finset.sum_comm

end Matrix
