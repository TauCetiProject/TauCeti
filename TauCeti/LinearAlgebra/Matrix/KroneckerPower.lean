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

If `Aᵀ * A = 1` then the Kronecker power satisfies the same identity: its `(v, u)` entry factors
as the product over `i` of the `(v i, u i)` entries of `Aᵀ * A`.

## Main definitions

* `Matrix.kroneckerPower`: the `κ`-indexed Kronecker power of a square matrix.

## Main results

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

/-- The Kronecker power of a matrix `A` with `Aᵀ * A = 1` satisfies the same identity. -/
theorem kroneckerPower_transpose_mul_self [CommSemiring R] [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] {A : Matrix ι ι R} (hA : Aᵀ * A = 1) :
    (A.kroneckerPower κ)ᵀ * A.kroneckerPower κ = 1 := by
  ext v u
  have hcol : ∀ i, ∑ c, A c (v i) * A c (u i) = if v i = u i then 1 else 0 := fun i => by
    rw [← Matrix.one_apply, ← hA, Matrix.mul_apply]
    simp [Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, kroneckerPower_apply,
    ← Finset.prod_mul_distrib]
  rw [← (Fintype.prod_sum fun i c => A c (v i) * A c (u i)), Fintype.prod_congr _ _ hcol,
    Fintype.prod_boole, Matrix.one_apply]
  simp only [← funext_iff]

end Matrix
