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
the orthogonal projector onto a line of `ℂ²`, records that reindexing rows and columns along
one equivalence preserves the trace, and relates double sums of `2 × 2` minor terms to products
of traces and traces of products.

## Main results

* `Matrix.trace_add_mul_add_mul`: the expansion of `trace ((M + N) * S * (M + N) * S)` into the
  two pure terms and twice the mixed term.
* `Matrix.trace_two_mul_sub_one`: `trace (2 P - 1) = 2 trace P - n` for an `n × n` matrix `P`.
* `Matrix.trace_reindex_self`: reindexing rows and columns along one equivalence preserves the
  trace.
* `Matrix.sum_diag_mul_diag`, `Matrix.sum_offDiag_mul_eq_trace_mul`, and
  `Matrix.sum_symmMinor_eq_two_mul_trace_sub`: double-sum identities for diagonal products,
  off-diagonal products, and symmetrized `2 × 2` minors.
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

/-- The double sum of products of diagonal entries of two square matrices is the product of their
traces. -/
theorem sum_diag_mul_diag (A : Matrix m m R) (C : Matrix n n R) :
    ∑ i, ∑ j, A i i * C j j = A.trace * C.trace := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Matrix.trace, Matrix.diag]

/-- The double sum of cross entries `A j i * C i j` is the trace of `A * C`. -/
theorem sum_offDiag_mul_eq_trace_mul (A : Matrix m n R) (C : Matrix n m R) :
    ∑ i, ∑ j, A j i * C i j = (A * C).trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_comm

/-- The double sum of symmetrized `2 × 2` minor terms equals
`2 * (A.trace * C.trace - (A * C).trace)`. -/
theorem sum_symmMinor_eq_two_mul_trace_sub {R : Type*} [CommRing R] (A C : Matrix m m R) :
    ∑ i, ∑ j, (A i i * C j j - A j i * C i j + C i i * A j j - C j i * A i j) =
      2 * (A.trace * C.trace - (A * C).trace) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_diag_mul_diag,
    sum_offDiag_mul_eq_trace_mul, trace_mul_comm C A]
  ring

end Matrix
