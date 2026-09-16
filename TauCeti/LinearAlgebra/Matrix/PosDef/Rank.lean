/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import TauCeti.LinearAlgebra.Matrix.PosDef.Basic

/-!
# Full-rank congruences of positive-definite matrices

For a rectangular matrix `B`, congruence sends a positive-definite matrix `A` to
`B * A * Bᴴ`.  The result is positive definite exactly when the rows of `B` are independent,
or equivalently when `B` has full row rank.  This file records those equivalences in the form
needed to transport positive-definite covariance matrices along surjective linear maps.

Mathlib proves the forward construction
`Matrix.PosDef.mul_mul_conjTranspose_same` from injectivity of `B.vecMul`.  The converse follows
because a positive-definite matrix is invertible: if two row vectors have the same product with
`B`, they also have the same product with `B * A * Bᴴ`, and invertibility makes them equal.

## Main results

* `Matrix.rank_eq_card_iff_vecMul_injective` characterizes full row rank by injectivity of right
  multiplication by the matrix.
* `Matrix.PosDef.mul_mul_conjTranspose_same_iff_vecMul_injective` characterizes when a rectangular
  congruence of a positive-definite matrix stays positive definite.
* `Matrix.PosDef.mul_mul_conjTranspose_same_iff_rank_eq` states the same criterion as full row
  rank.
* `Matrix.PosDef.mul_mul_transpose_same_iff_rank_eq` is the real-matrix form used for covariance
  matrices.

-/

public section

open scoped Matrix

namespace Matrix

variable {K : Type*} [Field K] {m n : Type*} [Fintype m] [Fintype n]

/-- A matrix has full row rank exactly when right multiplication by it is injective. -/
theorem rank_eq_card_iff_vecMul_injective (B : Matrix m n K) :
    B.rank = Fintype.card m ↔ Function.Injective B.vecMul := by
  rw [vecMul_injective_iff, rank_eq_finrank_span_row,
    linearIndependent_iff_card_eq_finrank_span, Set.finrank, eq_comm]

namespace PosDef

variable [PartialOrder K] [StarRing K]

/-- Congruence of a positive-definite matrix by a rectangular matrix is positive definite exactly
when right multiplication by that matrix is injective. -/
theorem mul_mul_conjTranspose_same_iff_vecMul_injective {A : Matrix n n K} (hA : A.PosDef)
    (B : Matrix m n K) :
    (B * A * Bᴴ).PosDef ↔ Function.Injective B.vecMul := by
  classical
  refine ⟨fun hBA => ?_, hA.mul_mul_conjTranspose_same⟩
  have hcongr : Function.Injective (B * A * Bᴴ).vecMul :=
    Matrix.vecMul_injective_of_isUnit hBA.isUnit
  intro x y hxy
  apply hcongr
  simpa only [vecMul_vecMul] using congrArg (fun z => (z ᵥ* A) ᵥ* Bᴴ) hxy

/-- Congruence of a positive-definite matrix by a rectangular matrix is positive definite exactly
when the rectangular matrix has full row rank. -/
theorem mul_mul_conjTranspose_same_iff_rank_eq {A : Matrix n n K} (hA : A.PosDef)
    (B : Matrix m n K) :
    (B * A * Bᴴ).PosDef ↔ B.rank = Fintype.card m := by
  rw [hA.mul_mul_conjTranspose_same_iff_vecMul_injective,
    rank_eq_card_iff_vecMul_injective]

end PosDef

end Matrix

namespace Matrix.PosDef

variable {m n : Type*} [Fintype m] [Fintype n]

/-- A real rectangular congruence `B * A * Bᵀ` of a positive-definite matrix is positive
definite exactly when `B` has full row rank. -/
theorem mul_mul_transpose_same_iff_rank_eq {A : Matrix n n ℝ} (hA : A.PosDef)
    (B : Matrix m n ℝ) :
    (B * A * Bᵀ).PosDef ↔ B.rank = Fintype.card m := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using
    hA.mul_mul_conjTranspose_same_iff_rank_eq B

end Matrix.PosDef
