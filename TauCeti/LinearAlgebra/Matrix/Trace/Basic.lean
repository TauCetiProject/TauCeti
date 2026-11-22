/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Reindex
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-!
# Traces of products alternating with a fixed matrix

Fix a matrix `S`. This file expands the quadratic map `M ↦ trace (M * S * M * S)` at a sum, so
that polarization recovers the symmetric bilinear map `(M, N) ↦ trace (M * S * N * S)` from it.
It also computes the trace of `2 P - 1`, which vanishes for a trace-one `2 × 2` matrix `P` such as
the orthogonal projector onto a line of `ℂ²`, and records that reindexing rows and columns along
one equivalence preserves the trace. Finally, two square matrices intertwined by a matrix whose
determinant is a non-zero-divisor have the same trace; over a domain this applies to every
intertwiner of nonzero determinant, such as the inclusion matrix of a full-rank sublattice.

## Main results

* `Matrix.trace_add_mul_add_mul`: the expansion of `trace ((M + N) * S * (M + N) * S)` into the
  two pure terms and twice the mixed term.
* `Matrix.trace_two_mul_sub_one`: `trace (2 P - 1) = 2 trace P - n` for an `n × n` matrix `P`.
* `Matrix.trace_reindex_self`: reindexing rows and columns along one equivalence preserves the
  trace.
* `Matrix.trace_eq_of_mul_eq_mul`: if `A * P = P * B` and `det P` is a non-zero-divisor, then
  `trace A = trace B`.
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

/-- **Intertwined matrices have equal traces.** If `A * P = P * B` and the determinant of `P` is a
non-zero-divisor, then `trace A = trace B`. The matrix `P` need not be invertible; over `ℤ`, for
instance, it may be the inclusion matrix of a sublattice of finite index. -/
theorem trace_eq_of_mul_eq_mul {R : Type*} [CommRing R] [DecidableEq n] {A B P : Matrix n n R}
    (hP : P.det ∈ nonZeroDivisors R) (h : A * P = P * B) : A.trace = B.trace := by
  -- multiply both traces by `det P` and move `P` across with its adjugate
  refine (mul_cancel_left_mem_nonZeroDivisors hP).1 ?_
  calc P.det * A.trace = (A * (P * P.adjugate)).trace := by
        rw [mul_adjugate, Matrix.mul_smul, Matrix.mul_one, trace_smul, smul_eq_mul]
    _ = (P.adjugate * (P * B)).trace := by
        rw [← Matrix.mul_assoc, h, trace_mul_comm]
    _ = P.det * B.trace := by
        rw [← Matrix.mul_assoc, adjugate_mul, Matrix.smul_mul, Matrix.one_mul, trace_smul,
          smul_eq_mul]

end Matrix
