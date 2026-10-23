/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Kronecker products of symmetric and positive definite matrices

The block-diagonal product `1 ⊗ₖ A` preserves positive definiteness over any star ring with
an additive order. Both index types may be infinite, since positive definiteness tests only
finitely supported vectors. This covers orthogonal sums of copies of one rational Gram matrix.
The symmetry result needs only multiplication, and the finite identity for the quadratic expression
holds over a nonassociative semiring with an arbitrary star operation.

## Main results

* `Matrix.IsSymm.kronecker`: the Kronecker product of symmetric matrices is symmetric.
* `Matrix.finsupp_sum_one_kronecker`: the finitely supported quadratic expression for `1 ⊗ₖ A`
  decomposes into the expressions for `A` on its blocks.
* `Matrix.PosDef.one_kronecker`: if `A` is positive definite, so is `1 ⊗ₖ A`.
-/

public section

open Matrix
open scoped Kronecker

namespace TauCeti

variable {R m n : Type*}

/-- The Kronecker product of symmetric matrices is symmetric. -/
theorem _root_.Matrix.IsSymm.kronecker [Mul R] {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsSymm) (hB : B.IsSymm) : (A ⊗ₖ B).IsSymm := by
  rw [IsSymm, ← kroneckerMap_transpose, hA.eq, hB.eq]

/-- The quadratic expression for `1 ⊗ₖ A` is the sum of those for `A` on the blocks. -/
theorem _root_.Matrix.star_dotProduct_one_kronecker_mulVec [NonAssocSemiring R] [Star R]
    [Fintype m] [DecidableEq m] [Fintype n] (A : Matrix n n R) (x : m × n → R) :
    star x ⬝ᵥ (((1 : Matrix m m R) ⊗ₖ A) *ᵥ x) =
      ∑ i, star (fun j => x (i, j)) ⬝ᵥ (A *ᵥ fun j => x (i, j)) := by
  simp [dotProduct, mulVec, Fintype.sum_prod_type, one_apply, ite_mul, Finset.sum_ite_eq]

/-- The finitely supported quadratic expression for `1 ⊗ₖ A` is the sum of those for `A`
on the blocks. -/
theorem _root_.Matrix.finsupp_sum_one_kronecker [NonAssocSemiring R] [Star R] [DecidableEq m]
    (A : Matrix n n R) (x : m × n →₀ R) :
    (x.sum fun i xi => x.sum fun j xj => star xi * ((1 : Matrix m m R) ⊗ₖ A) i j * xj) =
      x.curry.sum (fun _ y => y.sum fun i yi => y.sum fun j yj => star yi * A i j * yj) := by
  classical
  rw [← Finsupp.uncurry_curry x]
  simp only [Finsupp.sum_uncurry_index, Finsupp.curry_uncurry]
  refine Finsupp.sum_congr fun i hi => ?_
  refine Finsupp.sum_congr fun a ha => ?_
  simp [one_apply, mul_ite, ite_mul, Finsupp.sum, Finset.sum_ite_irrel,
    -Finsupp.support_curry, Finsupp.mem_support_iff.mp hi]

/-- If `A` is positive definite, then so is the block-diagonal matrix `1 ⊗ₖ A`. -/
theorem _root_.Matrix.PosDef.one_kronecker [Ring R] [PartialOrder R] [StarRing R]
    [IsOrderedAddMonoid R] [DecidableEq m] {A : Matrix n n R}
    (hA : A.PosDef) : ((1 : Matrix m m R) ⊗ₖ A).PosDef := by
  classical
  refine ⟨?_, fun x hx => ?_⟩
  · rw [Matrix.one_kronecker, isHermitian_reindex_iff, isHermitian_blockDiagonal_iff]
    exact fun _ => hA.isHermitian
  -- Group the test vector by blocks; each nonzero block contributes a positive term.
  have hc : x.curry ≠ 0 := by
    intro h
    apply hx
    ext ⟨i, j⟩
    exact congrArg (fun y : m →₀ n →₀ R => y i j) h
  rw [finsupp_sum_one_kronecker]
  exact Finsupp.sum_pos (fun i hi => hA.2 (Finsupp.mem_support_iff.mp hi)) hc

end TauCeti
