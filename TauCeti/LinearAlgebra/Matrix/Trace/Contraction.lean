/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Ring

/-!
# Contracting a family of matrices through its entry covariance

For a finite family of square matrices `E : ι → Matrix m m R`, the sums
`∑ p, trace (A * E p) • E p` and `∑ p, E p * M * E p` depend on the family only through the
entry covariance `∑ p, E p a b * E p c d`. This file writes their entries in terms of it, so
that a completeness relation for `E`, stated entrywise, evaluates both sums. It also writes the
bilinear form `u ⬝ᵥ M *ᵥ v` as the trace of `M` against the rank-one matrix `vecMulVec v u`,
which turns pairings with vectors into trace pairings.

## Main results

* `Matrix.sum_trace_mul_smul_apply`: the entries of `∑ p, trace (A * E p) • E p`.
* `Matrix.sum_mul_mul_apply`: the entries of `∑ p, E p * M * E p`.
* `Matrix.dotProduct_mulVec_eq_trace_vecMulVec_mul`: `u ⬝ᵥ M *ᵥ v = trace (vecMulVec v u * M)`.
-/

public section

namespace Matrix

variable {ι m R : Type*} [Fintype ι] [Fintype m]

/-- The entries of `∑ p, trace (A * E p) • E p` through the entry covariance
`∑ p, E p a b * E p c d` of the family `E`. -/
theorem sum_trace_mul_smul_apply [Semiring R] (E : ι → Matrix m m R) (A : Matrix m m R)
    (c d : m) :
    (∑ p, trace (A * E p) • E p) c d = ∑ a, ∑ b, A b a * ∑ p, E p a b * E p c d := by
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, trace, diag_apply, Matrix.mul_apply,
    Finset.sum_mul, Finset.mul_sum, mul_assoc]
  -- Reorder the sums over `(p, b, a)` to `(a, b, p)`: cycle to `(a, p, b)`, then swap `p` and `b`.
  rw [Finset.sum_comm_cycle]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm

/-- The entries of `∑ p, E p * M * E p` through the entry covariance `∑ p, E p a b * E p c d` of
the family `E`. -/
theorem sum_mul_mul_apply [CommSemiring R] (E : ι → Matrix m m R) (M : Matrix m m R) (a d : m) :
    (∑ p, E p * M * E p) a d = ∑ b, ∑ c, M b c * ∑ p, E p a b * E p c d := by
  simp only [Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  -- Reorder the sums over `(p, c, b)` to `(b, c, p)`: cycle to `(b, p, c)`, then swap `p` and `c`.
  rw [Finset.sum_comm_cycle]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_comm.trans <|
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring

/-- The bilinear form `u ⬝ᵥ M *ᵥ v` is the trace of `M` against the rank-one matrix
`vecMulVec v u`. -/
theorem dotProduct_mulVec_eq_trace_vecMulVec_mul [CommSemiring R] (u v : m → R)
    (M : Matrix m m R) : u ⬝ᵥ M *ᵥ v = trace (vecMulVec v u * M) := by
  rw [vecMulVec_mul, trace_vecMulVec, dotProduct_mulVec, dotProduct_comm]

end Matrix
