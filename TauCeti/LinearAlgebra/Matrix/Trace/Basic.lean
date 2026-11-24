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
* `Matrix.trace_mul_transpose_self_pos`: `0 < (A * Aᵀ).trace` for any nonzero matrix `A` over a
  linearly strict ordered ring.
* `Matrix.trace_list_prod_map_mapMatrix`: mapping a list of square matrices along a ring
  homomorphism commutes with taking the trace of its product.
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

/-- The trace of `A * Aᵀ` is strictly positive for any nonzero matrix `A` over a linearly strict
ordered ring. -/
theorem trace_mul_transpose_self_pos {R : Type*} [Ring R] [LinearOrder R] [IsStrictOrderedRing R]
    {A : Matrix m n R} (hA : A ≠ 0) : 0 < (A * Aᵀ).trace := by
  obtain ⟨i, j, hij⟩ : ∃ i j, A i j ≠ 0 := by
    by_contra! h
    exact hA (Matrix.ext h)
  simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_pos' (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
    ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ ↦ mul_self_nonneg _)
      ⟨j, Finset.mem_univ _, mul_self_pos.mpr hij⟩⟩

/-- Mapping a list of square matrices along a ring homomorphism commutes with taking the trace of
its product. -/
theorem trace_list_prod_map_mapMatrix {R S : Type*} [DecidableEq n] [Semiring R] [Semiring S]
    (f : R →+* S) (l : List (Matrix n n R)) :
    trace (l.map f.mapMatrix).prod = f (trace l.prod) := by
  rw [← map_list_prod, RingHom.mapMatrix_apply, ← AddMonoidHom.map_trace]

end Matrix
