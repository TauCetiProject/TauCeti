/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Characteristic roots of matrices over algebraically closed fields

Over an algebraically closed field, the characteristic polynomial of a square matrix of positive
size has a root. This file records that fact as a `Nonempty` instance on the root multiset, so that
families indexed by the characteristic roots, counted with algebraic multiplicity, have a nonempty
index type.

## Main results

* `Matrix.nonempty_roots_charpoly` — a square matrix of positive size over an algebraically closed
  field has a characteristic root.
* `Matrix.charpoly_roots_filter_ne_zero_mul_eq` — the nonzero characteristic roots of rectangular
  products `A * B` and `B * A` agree, counted with multiplicity.
-/

public section

open Polynomial

namespace Matrix

section RectangularProducts

variable {m n K : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
  [Field K] [DecidableEq K]

/-- Rectangular products `A * B` and `B * A` have the same nonzero characteristic roots,
counted with algebraic multiplicity. -/
theorem charpoly_roots_filter_ne_zero_mul_eq (A : Matrix m n K) (B : Matrix n m K) :
    Multiset.filter (fun z : K => z ≠ 0) (A * B).charpoly.roots =
      Multiset.filter (fun z : K => z ≠ 0) (B * A).charpoly.roots := by
  classical
  have hA_ne : (A * B).charpoly ≠ (0 : Polynomial K) :=
    (Matrix.charpoly_monic _).ne_zero
  have hB_ne : (B * A).charpoly ≠ (0 : Polynomial K) :=
    (Matrix.charpoly_monic _).ne_zero
  have hroots := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A B)
  rw [Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hA_ne),
      Polynomial.roots_mul
        (mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) hB_ne),
      Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hroots
  have hroots_nonzero :=
    congrArg (Multiset.filter (fun z : K => z ≠ 0)) hroots
  have hzero_roots (d : ℕ) :
      Multiset.filter (fun z : K => z ≠ 0) (d • ({0} : Multiset K)) = 0 := by
    induction d with
    | zero => simp
    | succ d ih => simp [succ_nsmul, ih]
  simp only [Multiset.filter_add, hzero_roots, zero_add] at hroots_nonzero
  exact hroots_nonzero

end RectangularProducts

variable {n K : Type*} [Fintype n] [DecidableEq n] [Nonempty n] [Field K] [IsAlgClosed K]
  [DecidableEq K]

/-- A square matrix of positive size over an algebraically closed field has a characteristic
root. -/
instance nonempty_roots_charpoly (A : Matrix n n K) : Nonempty A.charpoly.roots := by
  rw [← Fintype.card_pos_iff, Multiset.card_coe, IsAlgClosed.card_roots_eq_natDegree,
    charpoly_natDegree_eq_dim]
  exact Fintype.card_pos

end Matrix
