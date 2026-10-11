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

Mathlib's `Matrix.PosDef.kronecker` is stated over `RCLike` fields only. This file records the
block-diagonal case `1 ⊗ₖ A` over an arbitrary ordered commutative star ring, which covers
orthogonal sums of copies of one rational Gram matrix.

## Main results

* `Matrix.IsSymm.kronecker`: the Kronecker product of symmetric matrices is symmetric.
* `Matrix.PosDef.one_kronecker`: if `A` is positive definite, so is `1 ⊗ₖ A`.
-/

public section

open Matrix
open scoped Kronecker

namespace TauCeti

variable {R m n : Type*}

/-- The Kronecker product of symmetric matrices is symmetric. -/
theorem _root_.Matrix.IsSymm.kronecker [CommMagma R] {A : Matrix m m R} {B : Matrix n n R}
    (hA : A.IsSymm) (hB : B.IsSymm) : (A ⊗ₖ B).IsSymm := by
  rw [IsSymm, ← kroneckerMap_transpose, hA.eq, hB.eq]

/-- The quadratic form of `1 ⊗ₖ A` is the sum of the quadratic forms of `A` on the blocks. -/
theorem _root_.Matrix.star_dotProduct_one_kronecker_mulVec [CommRing R] [StarRing R] [Fintype m]
    [DecidableEq m] [Fintype n] (A : Matrix n n R) (x : m × n → R) :
    star x ⬝ᵥ (((1 : Matrix m m R) ⊗ₖ A) *ᵥ x) =
      ∑ i, star (fun j => x (i, j)) ⬝ᵥ (A *ᵥ fun j => x (i, j)) := by
  simp [dotProduct, mulVec, Fintype.sum_prod_type, one_apply, ite_mul, Finset.sum_ite_eq]

/-- If `A` is positive definite, then so is the block-diagonal matrix `1 ⊗ₖ A`. -/
theorem _root_.Matrix.PosDef.one_kronecker [CommRing R] [PartialOrder R] [StarRing R]
    [IsOrderedAddMonoid R] [Finite m] [DecidableEq m] [Finite n] {A : Matrix n n R}
    (hA : A.PosDef) : ((1 : Matrix m m R) ⊗ₖ A).PosDef := by
  have := Fintype.ofFinite m
  have := Fintype.ofFinite n
  refine posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun x hx => ?_⟩
  · rw [IsHermitian, conjTranspose_kronecker, conjTranspose_one, hA.isHermitian.eq]
  have hrow (i : m) : 0 ≤ star (fun j => x (i, j)) ⬝ᵥ (A *ᵥ fun j => x (i, j)) := by
    by_cases hi : (fun j => x (i, j)) = 0
    · simp [hi]
    · exact (hA.dotProduct_mulVec_pos hi).le
  obtain ⟨i, hi⟩ : ∃ i, (fun j => x (i, j)) ≠ 0 := by
    by_contra! h
    exact hx (funext fun ij => congrFun (h ij.1) ij.2)
  rw [star_dotProduct_one_kronecker_mulVec]
  exact Finset.sum_pos' (fun i _ => hrow i) ⟨i, Finset.mem_univ _, hA.dotProduct_mulVec_pos hi⟩

end TauCeti
