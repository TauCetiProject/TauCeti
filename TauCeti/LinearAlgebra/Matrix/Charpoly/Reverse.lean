/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# The reversed characteristic polynomial `det (1 - X A)` of a square matrix

For a square matrix `A` over a commutative ring, Mathlib's `Matrix.charpolyRev A` is the
determinant `det (1 - X A)`. It is the finite-dimensional case of the Fredholm determinant. In the
intended nonarchimedean setting, under suitable analytic hypotheses this extends to compact
operators on infinite-dimensional Banach spaces as a power series with constant coefficient `1`.
This file develops the finite-dimensional algebra of `det (1 - X A)` that such a theory reduces to.

In dimension `n = Fintype.card ι`, `det (1 - X A)` is the reflection `X ^ n · χ_A(1 / X)` of the
characteristic polynomial at degree `n` (`Matrix.charpolyRev_eq_reflect`). The reflection is
taken at `n` rather than at the actual degree, which is smaller when `A` is singular: for
`A = diag(a, 0)` one gets `1 - a X` in dimension two, and the zero eigenvalue is remembered only by
the dimension.

## Main results

* `Matrix.coeff_charpolyRev`: the `k`-th coefficient is `(-1) ^ k` times the sum of the `k × k`
  principal minors. In particular the constant coefficient is `1` and the coefficient in degree
  `Fintype.card ι` is `(-1) ^ Fintype.card ι * det A`.
* `Matrix.charpolyRev_map`, `Matrix.charpolyRev_transpose`, `Matrix.charpolyRev_reindex`:
  functoriality in the coefficient ring and invariance under transposition and relabelling.
* `Matrix.charpolyRev_fromBlocks_zero₂₁`, `Matrix.BlockTriangular.charpolyRev`: multiplicativity on
  block-triangular matrices, with `Matrix.charpolyRev_of_isUpperTriangular` and
  `Matrix.charpolyRev_diagonal` as special cases.
* `Matrix.charpolyRev_mul_comm`: `det (1 - X A B) = det (1 - X B A)` for rectangular matrices `A`
  and `B` of transposed shapes. Unlike `Matrix.charpoly_mul_comm'`, no power of `X` corrects for
  the different sizes of `A B` and `B A`.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§3–5.
-/

public section

open Polynomial

namespace Matrix

variable {ι κ R S : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [CommRing R] [CommRing S]

/-- `det (1 - X A)` is the reflection, at the dimension `Fintype.card ι`, of the characteristic
polynomial of `A`. The reflection is at the dimension, not at the degree of `det (1 - X A)`. -/
theorem charpolyRev_eq_reflect (A : Matrix ι ι R) :
    A.charpolyRev = A.charpoly.reflect (Fintype.card ι) := by
  nontriviality R
  rw [← reverse_charpoly, reverse, charpoly_natDegree_eq_dim]

/-- The degree of `det (1 - X A)` is at most the dimension. -/
theorem natDegree_charpolyRev_le (A : Matrix ι ι R) :
    A.charpolyRev.natDegree ≤ Fintype.card ι := by
  nontriviality R
  rw [← reverse_charpoly]
  exact (reverse_natDegree_le _).trans (charpoly_natDegree_eq_dim A).le

/-- **Principal-minor expansion.** The `k`-th coefficient of `det (1 - X A)` is `(-1) ^ k` times
the sum of the `k × k` principal minors of `A`. -/
theorem coeff_charpolyRev (A : Matrix ι ι R) (k : ℕ) :
    A.charpolyRev.coeff k = (-1) ^ k * ∑ s ∈ Finset.univ.powersetCard k,
      (A.submatrix (Subtype.val : s → ι) Subtype.val).det := by
  have h : A.charpolyRev = det (1 + (X : R[X]) • (-A).map C) := by
    rw [charpolyRev, sub_eq_add_neg, Matrix.map_neg _ (map_neg C), smul_neg]
  rw [h, coeff_det_one_add_X_smul_eq_sum_minors, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  simp only [submatrix_neg, Pi.neg_apply, det_neg, Fintype.card_coe,
    (Finset.mem_powersetCard.mp hs).2]

/-- The constant coefficient of `det (1 - X A)` is `1`. -/
@[simp]
theorem coeff_charpolyRev_zero (A : Matrix ι ι R) : A.charpolyRev.coeff 0 = 1 := by
  rw [coeff_zero_eq_eval_zero, eval_charpolyRev]

/-- The coefficient of `det (1 - X A)` in degree `Fintype.card ι` is `(-1) ^ Fintype.card ι` times
the determinant of `A`. -/
theorem coeff_charpolyRev_card (A : Matrix ι ι R) :
    A.charpolyRev.coeff (Fintype.card ι) = (-1) ^ Fintype.card ι * A.det := by
  rw [charpolyRev_eq_reflect, coeff_reflect, revAt_le le_rfl, Nat.sub_self,
    det_eq_sign_charpoly_coeff]
  simp [← mul_assoc, ← mul_pow]

/-- The coefficients of `det (1 - X A)` above the dimension vanish. -/
theorem coeff_charpolyRev_eq_zero (A : Matrix ι ι R) {k : ℕ} (hk : Fintype.card ι < k) :
    A.charpolyRev.coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt ((natDegree_charpolyRev_le A).trans_lt hk)

/-- `det (1 - X A)` commutes with ring homomorphisms of the coefficients. -/
theorem charpolyRev_map (A : Matrix ι ι R) (f : R →+* S) :
    (A.map f).charpolyRev = A.charpolyRev.map f := by
  rw [charpolyRev, charpolyRev, ← coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

/-- `det (1 - X A)` is unchanged by transposition. -/
@[simp]
theorem charpolyRev_transpose (A : Matrix ι ι R) : Aᵀ.charpolyRev = A.charpolyRev := by
  rw [charpolyRev_eq_reflect, charpolyRev_eq_reflect, charpoly_transpose]

/-- `det (1 - X A)` is unchanged by relabelling the rows and columns simultaneously. -/
theorem charpolyRev_reindex (e : ι ≃ κ) (A : Matrix ι ι R) :
    (reindex e e A).charpolyRev = A.charpolyRev := by
  rw [charpolyRev_eq_reflect, charpolyRev_eq_reflect, charpoly_reindex, Fintype.card_congr e]

/-- `det (1 - X A)` of an empty matrix is `1`. -/
@[simp]
theorem charpolyRev_isEmpty [IsEmpty ι] (A : Matrix ι ι R) : A.charpolyRev = 1 := by
  simp [charpolyRev]

/-- `det (1 - X · 0)` is `1` in every dimension. -/
@[simp]
theorem charpolyRev_zero : (0 : Matrix ι ι R).charpolyRev = 1 := by
  simp [charpolyRev]

/-- `det (1 - X A)` of a diagonal matrix is the product of the linear factors `1 - d i X`. -/
theorem charpolyRev_diagonal (d : ι → R) :
    (diagonal d).charpolyRev = ∏ i, (1 - C (d i) * X) := by
  rw [charpolyRev, diagonal_map (map_zero C), ← diagonal_smul, ← diagonal_one, diagonal_sub,
    det_diagonal]
  exact Finset.prod_congr rfl fun i _ ↦ by rw [Pi.smul_apply, smul_eq_mul, mul_comm]

/-- **Cyclicity.** `det (1 - X A B) = det (1 - X B A)` for rectangular matrices `A` and `B` of
transposed shapes. -/
theorem charpolyRev_mul_comm (A : Matrix ι κ R) (B : Matrix κ ι R) :
    (A * B).charpolyRev = (B * A).charpolyRev := by
  rw [charpolyRev, charpolyRev, Matrix.map_mul, Matrix.map_mul, ← smul_mul,
    det_one_sub_mul_comm, Matrix.mul_smul]

/-- **Block-triangular multiplicativity.** `det (1 - X A)` of a block upper-triangular matrix is the
product over its diagonal blocks. -/
@[simp]
theorem charpolyRev_fromBlocks_zero₂₁ (A : Matrix ι ι R) (B : Matrix ι κ R) (D : Matrix κ κ R) :
    (fromBlocks A B 0 D).charpolyRev = A.charpolyRev * D.charpolyRev := by
  simp only [charpolyRev, fromBlocks_map, Matrix.map_zero _ (map_zero C), fromBlocks_smul,
    smul_zero, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, neg_zero,
    add_zero, det_fromBlocks_zero₂₁]

/-- `det (1 - X A)` of a block lower-triangular matrix is the product over its diagonal blocks. -/
@[simp]
theorem charpolyRev_fromBlocks_zero₁₂ (A : Matrix ι ι R) (C' : Matrix κ ι R) (D : Matrix κ κ R) :
    (fromBlocks A 0 C' D).charpolyRev = A.charpolyRev * D.charpolyRev := by
  rw [← charpolyRev_transpose, fromBlocks_transpose, transpose_zero,
    charpolyRev_fromBlocks_zero₂₁, charpolyRev_transpose, charpolyRev_transpose]

/-- `det (1 - X A)` of a block-triangular matrix is the product of `det (1 - X A_a)` over its
diagonal blocks `A_a`. -/
theorem BlockTriangular.charpolyRev {α : Type*} [LinearOrder α] {b : ι → α} {A : Matrix ι ι R}
    (h : A.BlockTriangular b) :
    A.charpolyRev = ∏ a ∈ Finset.univ.image b, (A.toSquareBlock b a).charpolyRev := by
  have h' : (1 - (X : R[X]) • A.map C).BlockTriangular b :=
    blockTriangular_one.sub fun i j hij ↦ by simp [h hij]
  rw [Matrix.charpolyRev, h'.det]
  refine Finset.prod_congr rfl fun a _ ↦ congrArg det ?_
  ext i j
  simp [toSquareBlock_def, one_apply, Subtype.ext_iff]

/-- `det (1 - X A)` of an upper-triangular matrix is the product of the factors `1 - A i i X`. -/
theorem charpolyRev_of_isUpperTriangular [LinearOrder ι] {A : Matrix ι ι R}
    (h : A.IsUpperTriangular) : A.charpolyRev = ∏ i, (1 - C (A i i) * X) := by
  have h' : (1 - (X : R[X]) • A.map C).IsUpperTriangular :=
    blockTriangular_one.sub fun i j hij ↦ by simp [h hij]
  rw [Matrix.charpolyRev, det_of_isUpperTriangular h']
  exact Finset.prod_congr rfl fun i _ ↦ by simp [mul_comm (X : R[X])]

end Matrix
