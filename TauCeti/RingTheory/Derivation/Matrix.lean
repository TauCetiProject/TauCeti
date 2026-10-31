/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Derivations applied entrywise to matrices

A derivation `D` of a commutative algebra `A` acts on matrices over `A` entry by entry, through
`Matrix.map`. This entrywise action satisfies the Leibniz rule for matrix multiplication,
`(M * N).map D = M.map D * N + M * N.map D`, because each entry of a product is a sum of products of
entries.

A consequence is used to show that trace polynomials are invariant: if `D` acts on a square matrix
`M` as the commutator with some matrix `B`, so `M.map D = B * M - M * B`, then it acts on every
power `M ^ m` as the commutator with the same `B`. Since `D` commutes with the trace and the trace
of a commutator vanishes, `D` then kills every trace `(M ^ m).trace`.

## Main results

* `Derivation.map_matrix_mul`: the Leibniz rule for the entrywise action on matrix products.
* `Derivation.map_matrix_pow_of_map_eq_mul_sub_mul`: if `D` acts on `M` as the commutator with `B`,
  it acts on each power of `M` as the commutator with `B`.
* `Derivation.trace_pow_eq_zero_of_map_eq_mul_sub_mul`: under the same hypothesis, `D` kills the
  traces of the powers of `M`.
-/

public section

namespace Derivation

variable {R A : Type*} [CommSemiring R]

section CommSemiring

variable [CommSemiring A] [Algebra R A] (D : Derivation R A A)

/-- **The Leibniz rule for matrices**: a derivation applied entrywise to a product of matrices is
`M.map D * N + M * N.map D`. -/
theorem map_matrix_mul {l m n : Type*} [Fintype m] (M : Matrix l m A) (N : Matrix m n A) :
    (M * N).map D = M.map D * N + M * N.map D := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, map_sum, leibniz, smul_eq_mul,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ ↦ by ring

end CommSemiring

variable [CommRing A] [Algebra R A] (D : Derivation R A A) {n : Type*} [Fintype n] [DecidableEq n]

/-- If a derivation acts on a square matrix `M` as the commutator with `B`, then it acts on every
power of `M` as the commutator with `B`. -/
theorem map_matrix_pow_of_map_eq_mul_sub_mul {M B : Matrix n n A} (h : M.map D = B * M - M * B)
    (m : ℕ) : (M ^ m).map D = B * M ^ m - M ^ m * B := by
  induction m with
  | zero =>
    ext i j
    by_cases hij : i = j <;> simp [hij]
  | succ m ih =>
    rw [pow_succ, map_matrix_mul, ih, h]
    simp only [sub_mul, mul_sub, mul_assoc]
    abel

/-- If a derivation acts on a square matrix `M` as the commutator with `B`, then it kills the
trace of every power of `M`. -/
theorem trace_pow_eq_zero_of_map_eq_mul_sub_mul {M B : Matrix n n A}
    (h : M.map D = B * M - M * B) (m : ℕ) : D (M ^ m).trace = 0 := by
  rw [AddMonoidHom.map_trace, map_matrix_pow_of_map_eq_mul_sub_mul D h, Matrix.trace_sub,
    Matrix.trace_mul_comm, sub_self]

end Derivation
