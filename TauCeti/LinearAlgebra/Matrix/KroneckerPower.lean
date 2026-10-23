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

For a square matrix `A` indexed by `ι` and a finite type `κ`, the Kronecker power
`Matrix.kroneckerPower κ A` is the matrix indexed by `κ → ι` whose `(v, u)` entry is
`∏ i, A (v i) (u i)`. It is the matrix of `A` acting in every factor of the `κ`-indexed tensor
power, in the monomial basis.

The Kronecker power is multiplicative and commutes with transposition, so if `Aᵀ * A = 1` then
the Kronecker power satisfies the same identity.

## Main definitions

* `Matrix.kroneckerPower`: the `κ`-indexed Kronecker power of a square matrix.

## Main results

* `Matrix.kroneckerPower_mul`, `Matrix.kroneckerPower_one`, `Matrix.kroneckerPower_transpose`:
  the Kronecker power is multiplicative, sends `1` to `1` and commutes with transposition.
* `Matrix.kroneckerPower_transpose_mul_self`: the Kronecker power of a matrix with `Aᵀ * A = 1`
  satisfies the same identity.
-/

public section

namespace Matrix

variable {R : Type*} {ι : Type*} (κ : Type*)

/-- The **Kronecker power** of a square matrix `A` indexed by `ι`: the matrix indexed by `κ → ι`
whose `(v, u)` entry is `∏ i, A (v i) (u i)`, the matrix of `A` acting in every factor of the
`κ`-indexed tensor power. -/
def kroneckerPower [CommMonoid R] [Fintype κ] (A : Matrix ι ι R) : Matrix (κ → ι) (κ → ι) R :=
  Matrix.of fun v u => ∏ i, A (v i) (u i)

@[simp]
theorem kroneckerPower_apply [CommMonoid R] [Fintype κ] (A : Matrix ι ι R) (v u : κ → ι) :
    A.kroneckerPower κ v u = ∏ i, A (v i) (u i) :=
  (rfl)

variable {κ}

/-- The Kronecker power commutes with transposition. -/
@[simp]
theorem kroneckerPower_transpose [CommMonoid R] [Fintype κ] (A : Matrix ι ι R) :
    (A.kroneckerPower κ)ᵀ = Aᵀ.kroneckerPower κ :=
  (rfl)

/-- The Kronecker power of the identity matrix is the identity matrix. -/
@[simp]
theorem kroneckerPower_one [CommMonoidWithZero R] [DecidableEq ι] [Fintype κ] :
    (1 : Matrix ι ι R).kroneckerPower κ = 1 := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.one_apply, Fintype.prod_boole, ← funext_iff]

/-- The Kronecker power is multiplicative: the `(v, u)` entry of `A^{⊗κ} * B^{⊗κ}` expands, by
distributing the product over the sums, into the product of the entries of `A * B`. -/
theorem kroneckerPower_mul [CommSemiring R] [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A B : Matrix ι ι R) :
    (A * B).kroneckerPower κ = A.kroneckerPower κ * B.kroneckerPower κ := by
  ext v u
  simp only [kroneckerPower_apply, Matrix.mul_apply, Fintype.prod_sum, ← Finset.prod_mul_distrib]

/-- The Kronecker power of a matrix `A` with `Aᵀ * A = 1` satisfies the same identity. -/
theorem kroneckerPower_transpose_mul_self [CommSemiring R] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix ι ι R} (hA : Aᵀ * A = 1) :
    (A.kroneckerPower κ)ᵀ * A.kroneckerPower κ = 1 := by
  rw [kroneckerPower_transpose, ← kroneckerPower_mul, hA, kroneckerPower_one]

end Matrix
