/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Cluster.ExchangeMatrix.Mutation.Basic
public import Mathlib.LinearAlgebra.Matrix.Symmetric

import Mathlib.Algebra.Order.Ring.Abs

/-!
# Cartan companions of integer matrices

The Cartan companion has diagonal entries two and off-diagonal entries `-|bᵢⱼ|`.
Every positive skew-symmetrizer of an exchange matrix symmetrizes its companion.
The construction commutes with transposition and injective simultaneous restriction; its
block formula applies even when the off-diagonal blocks are nonzero. Source or sink mutation
preserves the companion. No finite-index
hypothesis is needed except for the matrix product with a diagonal symmetrizer.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*,
  Inventiones Mathematicae 154 (2003), §1.
-/

public section

namespace Matrix

variable {K : Type*} [DecidableEq K]

/-- The Cartan companion of an integer matrix has diagonal two and negative absolute
values off the diagonal. -/
def cartanCompanion (B : Matrix K K ℤ) : Matrix K K ℤ :=
  of fun i j ↦ if i = j then 2 else -|B i j|

/-- The entries of the Cartan companion. -/
@[grind =]
theorem cartanCompanion_apply (B : Matrix K K ℤ) (i j : K) :
    B.cartanCompanion i j = if i = j then 2 else -|B i j| := by rfl

/-- The diagonal entries of a Cartan companion are two. -/
@[simp]
theorem cartanCompanion_apply_self (B : Matrix K K ℤ) (i : K) :
    B.cartanCompanion i i = 2 := by simp [cartanCompanion_apply]

/-- An off-diagonal entry of a Cartan companion is the negative absolute value. -/
@[simp]
theorem cartanCompanion_apply_of_ne (B : Matrix K K ℤ) {i j : K} (hij : i ≠ j) :
    B.cartanCompanion i j = -|B i j| := by simp [cartanCompanion_apply, hij]

/-- A companion entry vanishes exactly at an off-diagonal zero of the original matrix. -/
@[simp]
theorem cartanCompanion_apply_eq_zero_iff (B : Matrix K K ℤ) (i j : K) :
    B.cartanCompanion i j = 0 ↔ i ≠ j ∧ B i j = 0 := by
  by_cases hij : i = j <;> simp [hij]

/-- Off-diagonal entries of the Cartan companion are nonpositive. -/
theorem cartanCompanion_nonpos_of_ne (B : Matrix K K ℤ) {i j : K} (hij : i ≠ j) :
    B.cartanCompanion i j ≤ 0 := by simp [hij]

/-- The companion of the zero matrix is diagonal with entries two. -/
@[simp]
theorem cartanCompanion_zero : (0 : Matrix K K ℤ).cartanCompanion = diagonal (fun _ ↦ 2) := by
  ext i j
  simp [cartanCompanion_apply, diagonal_apply]

/-- Negating a matrix does not change its Cartan companion. -/
@[simp]
theorem cartanCompanion_neg (B : Matrix K K ℤ) : (-B).cartanCompanion = B.cartanCompanion := by
  ext i j
  simp [cartanCompanion_apply]

/-- The Cartan companion commutes with transposition. -/
theorem transpose_cartanCompanion (B : Matrix K K ℤ) :
    B.cartanCompanionᵀ = Bᵀ.cartanCompanion := by
  ext i j
  simp [cartanCompanion_apply, eq_comm]

/-- Simultaneous restriction along an injective map commutes with taking companions. -/
theorem cartanCompanion_submatrix {L : Type*} [DecidableEq L] (B : Matrix K K ℤ)
    {e : L → K} (he : Function.Injective e) :
    (B.submatrix e e).cartanCompanion = B.cartanCompanion.submatrix e e := by
  ext i j
  simp [cartanCompanion_apply, he.eq_iff]

/-- The companion of a block matrix takes companions on its diagonal blocks and negative
entrywise absolute values on its off-diagonal blocks. -/
@[simp]
theorem cartanCompanion_fromBlocks {L : Type*} [DecidableEq L]
    (A : Matrix K K ℤ) (B : Matrix K L ℤ) (C : Matrix L K ℤ) (D : Matrix L L ℤ) :
    (fromBlocks A B C D).cartanCompanion =
      fromBlocks A.cartanCompanion (B.map fun z ↦ -|z|) (C.map fun z ↦ -|z|)
        D.cartanCompanion := by
  ext (i | i) (j | j) <;> simp [cartanCompanion_apply]

namespace IsSkewSymmetrizer

/-- A source or sink mutation preserves the Cartan companion. -/
theorem cartanCompanion_matrixMutation_of_row_nonneg_or_nonpos
    {B : Matrix K K ℤ} {s : K → ℤ} (h : B.IsSkewSymmetrizer s) (k : K)
    (hk : (∀ l, 0 ≤ B k l) ∨ ∀ l, B k l ≤ 0) :
    (TauCeti.matrixMutation (Function.Embedding.refl K) B k).cartanCompanion =
      B.cartanCompanion := by
  ext i j
  simp only [cartanCompanion_apply]
  split_ifs with hij
  · rfl
  · rw [h.matrixMutation_apply_of_row_nonneg_or_nonpos k i j hk]
    split_ifs <;> simp


/-- A positive skew-symmetrizer gives symmetric weighted entries in the Cartan companion. -/
theorem mul_cartanCompanion_apply {B : Matrix K K ℤ} {s : K → ℤ}
    (h : B.IsSkewSymmetrizer s) (i j : K) :
    s i * B.cartanCompanion i j = s j * B.cartanCompanion j i := by
  by_cases hij : i = j
  · subst j
    rfl
  · have habs := congrArg abs (h.mul_apply i j)
    simp only [abs_mul, abs_of_pos (h.pos i), abs_of_pos (h.pos j), abs_neg] at habs
    simpa [hij, Ne.symm hij] using congrArg Neg.neg habs

/-- Scaling the rows of the Cartan companion by a positive skew-symmetrizer gives a
symmetric matrix. -/
theorem isSymm_diagonal_mul_cartanCompanion [Fintype K] {B : Matrix K K ℤ} {s : K → ℤ}
    (h : B.IsSkewSymmetrizer s) : (diagonal s * B.cartanCompanion).IsSymm := by
  ext i j
  simpa only [transpose_apply, diagonal_mul] using h.mul_cartanCompanion_apply j i

end IsSkewSymmetrizer

end Matrix
