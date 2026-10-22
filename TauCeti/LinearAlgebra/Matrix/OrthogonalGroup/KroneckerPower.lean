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
# Kronecker powers of orthogonal matrices

For a square matrix `A` indexed by `ι` and a finite type `κ`, the Kronecker power of `A` is the
matrix `Matrix.of fun v u : κ → ι => ∏ i, A (v i) (u i)`, the matrix of `A` acting diagonally on
the `κ`-indexed tensor power in the monomial basis. If `Aᵀ * A = 1` then the Kronecker power
satisfies the same identity: its `(v, u)` entry factors as the product over `i` of the
`(v i, u i)` entries of `Aᵀ * A`.

## Main results

* `Matrix.kroneckerPower_transpose_mul_self`: the Kronecker power of a matrix with `Aᵀ * A = 1`
  satisfies the same identity.
-/

public section

namespace Matrix

variable {R : Type*} [CommSemiring R] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- The Kronecker power `Matrix.of fun v u : κ → ι => ∏ i, A (v i) (u i)` of a matrix `A` with
`Aᵀ * A = 1` satisfies the same identity. -/
theorem kroneckerPower_transpose_mul_self {A : Matrix ι ι R} (hA : Aᵀ * A = 1) :
    (Matrix.of fun v u : κ → ι => ∏ i, A (v i) (u i))ᵀ *
      Matrix.of (fun v u : κ → ι => ∏ i, A (v i) (u i)) = 1 := by
  ext v u
  have hcol : ∀ i, ∑ c, A c (v i) * A c (u i) = if v i = u i then 1 else 0 := fun i => by
    rw [← Matrix.one_apply, ← hA, Matrix.mul_apply]
    simp [Matrix.transpose_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, ← Finset.prod_mul_distrib]
  rw [← (Fintype.prod_sum fun i c => A c (v i) * A c (u i)), Fintype.prod_congr _ _ hcol,
    Fintype.prod_boole, Matrix.one_apply]
  simp only [← funext_iff]

end Matrix
