/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.Matrix.Block

/-!
# Gauss sums of quadratic forms over a finite semiring

Let `S` be a finite commutative semiring and `ψ` an additive character of `S`. The Gauss sum of a
square matrix `A` over `S` is `∑_x ψ(xᵀ A x)`, the sum over all vectors `x` of the character at the
quadratic form of `A`. This file proves its two structural properties:

* it is invariant under congruence `A ↦ Pᵀ A P` by a matrix `P` whose action on vectors is
  bijective (`Matrix.sum_addChar_dotProduct_transpose_mul_mul_mulVec`), so the Gauss sum of the
  Gram matrix of a bilinear form on a free module does not depend on the basis;
* it is multiplicative over block diagonal matrices
  (`Matrix.sum_addChar_dotProduct_fromBlocks_zero_zero_mulVec`), so the Gauss sum of an orthogonal
  sum of forms is the product of their Gauss sums.

The evaluations of such sums at odd moduli are in `TauCeti.NumberTheory.QuadraticForm.GaussSum`.

## Main results

* `Matrix.sum_addChar_dotProduct_transpose_mul_mul_mulVec`: invariance under congruence.
* `Matrix.sum_addChar_dotProduct_fromBlocks_zero_zero_mulVec`: multiplicativity over block
  diagonal matrices.
-/

public section

open scoped Matrix

namespace Matrix

variable {m n S T : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  [CommSemiring S] [Fintype S] [CommSemiring T]
  (ψ : AddChar S T)

/-- **Gauss sums are invariant under congruence.** If `x ↦ P x` is a bijection from `n`-vectors to
`m`-vectors over a finite semiring `S`, then the Gauss sum `∑_x ψ(xᵀ Pᵀ A P x)` of `Pᵀ A P` is that
of `A`, for every additive character `ψ` of `S`. -/
theorem sum_addChar_dotProduct_transpose_mul_mul_mulVec (A : Matrix m m S) {P : Matrix m n S}
    (hP : Function.Bijective P.mulVec) :
    ∑ x : n → S, ψ (x ⬝ᵥ (Pᵀ * A * P) *ᵥ x) = ∑ y : m → S, ψ (y ⬝ᵥ A *ᵥ y) := by
  have hx (x : n → S) : x ⬝ᵥ (Pᵀ * A * P) *ᵥ x = P *ᵥ x ⬝ᵥ A *ᵥ (P *ᵥ x) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  simp only [hx]
  exact hP.sum_comp fun y ↦ ψ (y ⬝ᵥ A *ᵥ y)

/-- **Gauss sums are multiplicative over block diagonal matrices.** The Gauss sum of the block
diagonal matrix with blocks `A` and `D` over a finite semiring is the product of the Gauss sums of
`A` and `D`. -/
theorem sum_addChar_dotProduct_fromBlocks_zero_zero_mulVec (A : Matrix m m S)
    (D : Matrix n n S) :
    ∑ x : m ⊕ n → S, ψ (x ⬝ᵥ fromBlocks A 0 0 D *ᵥ x) =
      (∑ x : m → S, ψ (x ⬝ᵥ A *ᵥ x)) * ∑ y : n → S, ψ (y ⬝ᵥ D *ᵥ y) := by
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type',
    ← (Equiv.sumArrowEquivProdArrow m n S).symm.sum_comp]
  refine Fintype.sum_congr _ _ fun p ↦ ?_
  have hp : (Equiv.sumArrowEquivProdArrow m n S).symm p = Sum.elim p.1 p.2 := by
    ext (i | i) <;> rfl
  rw [hp, fromBlocks_mulVec, sumElim_dotProduct_sumElim, ← AddChar.map_add_eq_mul]
  simp [Function.comp_def]

end Matrix
