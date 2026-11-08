/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import TauCeti.Algebra.Group.AddChar

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
  sum of forms is the product of their Gauss sums; for a diagonal matrix it is the product of the
  one-variable sums `∑_y ψ(d y²)` (`Matrix.sum_addChar_dotProduct_diagonal_mulVec`).

The Gauss sum of the Gram matrix of a bilinear form, reduced along a ring homomorphism to `S`,
is therefore the same in every basis
(`LinearMap.BilinForm.sum_addChar_dotProduct_toMatrix_map_mulVec_eq`).

The evaluations of such sums at odd moduli are in `TauCeti.NumberTheory.QuadraticForm.GaussSum`.

## Main results

* `Matrix.sum_addChar_dotProduct_transpose_mul_mul_mulVec`: invariance under congruence.
* `Matrix.sum_addChar_dotProduct_fromBlocks_zero_zero_mulVec`: multiplicativity over block
  diagonal matrices.
* `Matrix.sum_addChar_dotProduct_diagonal_mulVec`: the Gauss sum of a diagonal matrix.
* `LinearMap.BilinForm.sum_addChar_dotProduct_toMatrix_map_mulVec_eq`: the Gauss sum of a Gram
  matrix does not depend on the basis.
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

/-- **The Gauss sum of a diagonal matrix** is the product of the one-variable Gauss sums of its
diagonal entries. -/
theorem sum_addChar_dotProduct_diagonal_mulVec (d : n → S) :
    ∑ x : n → S, ψ (x ⬝ᵥ diagonal d *ᵥ x) = ∏ i, ∑ y : S, ψ (d i * y ^ 2) := by
  rw [Fintype.prod_sum]
  refine Fintype.sum_congr _ _ fun x ↦ ?_
  simp only [mulVec_diagonal, dotProduct, ← AddChar.map_sum_eq_prod]
  exact congrArg ψ (Finset.sum_congr rfl fun i _ ↦ by ring)

end Matrix

open Module
open LinearMap (BilinForm)

namespace LinearMap.BilinForm

variable {R M S T ι κ : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring S]
  [Fintype S] [CommSemiring T] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **The Gauss sum of a Gram matrix does not depend on the basis.** Reduce the Gram matrices of
a bilinear form `B` in two finite bases `b` and `c` along a ring homomorphism `f` to a finite
semiring `S`. Their Gauss sums for an additive character `ψ` of `S` agree, because the reduced
change of basis matrix is invertible. -/
theorem sum_addChar_dotProduct_toMatrix_map_mulVec_eq (B : BilinForm R M) (b : Basis ι R M)
    (c : Basis κ R M) (f : R →+* S) (ψ : AddChar S T) :
    ∑ x : κ → S, ψ (x ⬝ᵥ (B.toMatrix c).map f *ᵥ x) =
      ∑ x : ι → S, ψ (x ⬝ᵥ (B.toMatrix b).map f *ᵥ x) := by
  have hbij : Function.Bijective ((b.toMatrix c).map f).mulVec := by
    refine Function.bijective_iff_has_inverse.mpr
      ⟨((c.toMatrix b).map f).mulVec, fun x ↦ ?_, fun x ↦ ?_⟩ <;>
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, Basis.toMatrix_mul_toMatrix_flip,
      Matrix.map_one _ (map_zero f) (map_one f), Matrix.one_mulVec]
  rw [← toMatrix_mul_basis_toMatrix b c B, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
    Matrix.sum_addChar_dotProduct_transpose_mul_mul_mulVec ψ _ hbij]

end LinearMap.BilinForm
