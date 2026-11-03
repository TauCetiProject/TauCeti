/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.LinearCombination

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

Let `S` be an `A`-algebra with a basis `b`, and let `D'` be a derivation of `S` extending `D`, in
the sense that `D' (algebraMap A S a) = algebraMap A S (D a)`. Then `D'` acts on coordinates in
`b` as `D` plus the connection matrix `Γ` whose columns are the coordinates of the `D' (b q)`.
Consequently `D`, applied entrywise to the matrix of multiplication by `s`, gives the matrix of
multiplication by `D' s` plus the commutator of the matrix of `s` with `Γ`.

## Main results

* `Derivation.map_matrix_mul`: the Leibniz rule for the entrywise action on matrix products.
* `Derivation.map_matrix_pow_of_map_eq_mul_sub_mul`: if `D` acts on `M` as the commutator with `B`,
  it acts on each power of `M` as the commutator with `B`.
* `Derivation.trace_pow_eq_zero_of_map_eq_mul_sub_mul`: under the same hypothesis, `D` kills the
  traces of the powers of `M`.
* `Derivation.basis_repr_apply`: the coordinates of `D' x` in a basis, for a derivation `D'`
  extending `D`.
* `Derivation.map_leftMulMatrix`: the entrywise derivative of the matrix of multiplication.
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

section Basis

variable {S : Type*} [CommRing S] [Algebra A S] [Algebra R S] (D' : Derivation R S S)
  (hD : ∀ a, D' (algebraMap A S a) = algebraMap A S (D a))

include hD

/-- In a basis `b`, the coordinates of `D' x` are the derivatives of the coordinates of `x` plus
the connection term `∑ r, b.repr x r * b.repr (D' (b r)) p`. -/
theorem basis_repr_apply {ι : Type*} [Fintype ι] (b : Module.Basis ι A S) (x : S) (p : ι) :
    b.repr (D' x) p = D (b.repr x p) + ∑ r, b.repr x r * b.repr (D' (b r)) p := by
  classical
  have hsmul (c : A) (y : S) : D' (c • y) = c • D' y + D c • y := by
    rw [Algebra.smul_def, leibniz, hD, smul_eq_mul, smul_eq_mul, mul_comm y, ← Algebra.smul_def,
      ← Algebra.smul_def]
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum, map_sum, Finset.sum_apply']
  simp only [hsmul, map_add, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [add_comm]

/-- In a basis `b`, the entrywise derivative of the matrix of multiplication by `s` is the matrix
of multiplication by `D' s` plus the commutator of that matrix with the connection matrix of
`D'` in `b`. -/
theorem map_leftMulMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι A S) (s : S) :
    (Algebra.leftMulMatrix b s).map D = Algebra.leftMulMatrix b (D' s) +
      (Algebra.leftMulMatrix b s * (Matrix.of fun p q => b.repr (D' (b q)) p) -
        (Matrix.of fun p q => b.repr (D' (b q)) p) * Algebra.leftMulMatrix b s) := by
  ext p q
  have h := basis_repr_apply D D' hD b (s * b q) p
  rw [leibniz, smul_eq_mul, smul_eq_mul, mul_comm (b q), map_add, Finsupp.add_apply,
    ← Algebra.leftMulMatrix_mulVec_repr] at h
  simp only [← Algebra.leftMulMatrix_eq_repr_mul, Matrix.mulVec, dotProduct] at h
  simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply,
    Matrix.of_apply]
  simp only [mul_comm (Algebra.leftMulMatrix b s _ q)] at h
  linear_combination -h

end Basis

end Derivation
