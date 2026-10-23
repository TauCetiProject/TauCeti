/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul

/-!
# Kronecker powers of matrices

For a matrix `A` with rows indexed by `m`, columns indexed by `n` and a finite type `κ`, the
Kronecker power `Matrix.kroneckerPower κ A` is the matrix with rows indexed by `κ → m` and columns
indexed by `κ → n` whose `(v, u)` entry is `∏ i, A (v i) (u i)`. It is the matrix of `A` acting in
every factor of the `κ`-indexed tensor power, in the monomial bases.

The Kronecker power is multiplicative and commutes with transposition, so if `Aᵀ * A = 1` then
the Kronecker power satisfies the same identity.

## Main definitions

* `Matrix.kroneckerPower`: the `κ`-indexed Kronecker power of a matrix.

## Main results

* `Matrix.kroneckerPower_mul`, `Matrix.kroneckerPower_one`, `Matrix.transpose_kroneckerPower`:
  the Kronecker power is multiplicative, sends `1` to `1` and commutes with transposition.
* `Matrix.transpose_kroneckerPower_mul_self`: the Kronecker power of a matrix with `Aᵀ * A = 1`
  satisfies the same identity.
-/

public section

namespace Matrix

variable {R : Type*} {l m n : Type*} (κ : Type*)

/-- The **Kronecker power** of a matrix `A : Matrix m n R`: the matrix with rows indexed by
`κ → m` and columns indexed by `κ → n` whose `(v, u)` entry is `∏ i, A (v i) (u i)`, the matrix of
`A` acting in every factor of the `κ`-indexed tensor power. -/
def kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix m n R) : Matrix (κ → m) (κ → n) R :=
  Matrix.of fun v u => ∏ i, A (v i) (u i)

@[simp]
theorem kroneckerPower_apply [CommMonoid R] [Fintype κ] (A : Matrix m n R) (v : κ → m)
    (u : κ → n) :
    A.kroneckerPower κ v u = ∏ i, A (v i) (u i) :=
  (rfl)

variable {κ}

/-- The Kronecker power commutes with transposition. -/
@[simp]
theorem transpose_kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix m n R) :
    (A.kroneckerPower κ)ᵀ = Aᵀ.kroneckerPower κ :=
  (rfl)

/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem kroneckerPower_one [CommMonoidWithZero R] [DecidableEq n] [Fintype κ] :
    (1 : Matrix n n R).kroneckerPower κ = 1 := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

/-- The Kronecker power is multiplicative: the `(v, u)` entry of `A^{⊗κ} * B^{⊗κ}` expands, by
distributing the product over the sums, into the product of the entries of `A * B`. -/
theorem kroneckerPower_mul [CommSemiring R] [Fintype m] [Fintype κ] [DecidableEq κ]
    (A : Matrix l m R) (B : Matrix m n R) :
    (A * B).kroneckerPower κ = A.kroneckerPower κ * B.kroneckerPower κ := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.mul_apply, Fintype.prod_sum, ← Finset.prod_mul_distrib]

/-- The Kronecker power of a matrix `A` with `Aᵀ * A = 1` satisfies the same identity. -/
theorem transpose_kroneckerPower_mul_self [CommSemiring R] [Fintype n] [DecidableEq n]
    [Fintype κ] [DecidableEq κ] {A : Matrix n n R} (hA : Aᵀ * A = 1) :
    (A.kroneckerPower κ)ᵀ * A.kroneckerPower κ = 1 := by
  rw [transpose_kroneckerPower, ← kroneckerPower_mul, hA, kroneckerPower_one]

end Matrix
