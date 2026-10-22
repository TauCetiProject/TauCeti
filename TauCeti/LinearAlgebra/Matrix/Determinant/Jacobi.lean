/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Sort
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# Jacobi's complementary minor theorem

For a square matrix `A` over a commutative ring and two finite sets `I` and `J` of row and column
indices with `#I = #J = k`, Jacobi's complementary minor theorem relates the minor of the adjugate
on the complementary index sets to the complementary minor of `A`:

`det A * det ((adj A)[Jᶜ, Iᶜ]) = (-1) ^ (∑ I + ∑ J) * (det A) ^ (n - k) * det (A[I, J])`.

Here `A[I, J]` denotes the submatrix with rows `I` and columns `J`, both listed in increasing order,
and the exponent `∑ I` is the sum of the indices in `I`.  The sign is the relative sign of the
shuffles that list `I` and `J` before their complements.

The theorem is the key step in passing between the complete-homogeneous Toeplitz matrix and its
inverse, and hence in the dual Jacobi--Trudi formula for Schur polynomials.  For `k = n - 1` it is
the cofactor formula for an entry of the adjugate.

## Main results

* `Matrix.det_mul_det_submatrix_adjugate`: Jacobi's complementary minor theorem in adjugate form.
* `Matrix.det_submatrix_equiv`: reindexing the rows and columns of a determinant by two different
  equivalences multiplies it by the sign of their relative permutation.
* `Equiv.Perm.sign_eq_prod_ite`: the sign of a permutation as a product over its inversions.
* `Equiv.Perm.sign_shuffle`: the sign of a shuffle permutation is a power of `-1`.
-/

public section

open Equiv Finset

namespace Equiv.Perm

variable {n k : ℕ}

/-- The sign of a permutation of `Fin n`, written as a product over its inversions. -/
theorem sign_eq_prod_ite (σ : Perm (Fin n)) :
    Perm.sign σ = ∏ y, ∏ x, if x < y ∧ σ y < σ x then -1 else 1 := by
  rw [σ.sign_eq_prod_prod_Iio]
  refine prod_congr rfl fun y _ ↦ ?_
  rw [← filter_gt_eq_Iio, prod_filter]
  refine prod_congr rfl fun x _ ↦ ?_
  split_ifs <;> grind [EmbeddingLike.apply_eq_iff_eq]

/-- The sign of a shuffle permutation.  Let `e : Fin k ⊕ Fin m ≃ Fin n` be increasing on each
summand, so that the images of `Sum.inl` form a `k`-element set `I` and the images of `Sum.inr`
form its complement.  Then the sign of the shuffle, viewed as a permutation of `Fin k ⊕ Fin m`,
is `(-1)` raised to the sum of the elements of `I` plus the sum of the positions in the first
summand. -/
theorem sign_shuffle {m : ℕ} (h : k + m = n) (e : Fin k ⊕ Fin m ≃ Fin n)
    (hl : StrictMono (e ∘ Sum.inl)) (hr : StrictMono (e ∘ Sum.inr)) :
    Perm.sign ((finSumFinEquiv.trans (finCongr h)).symm.trans e) =
      (-1) ^ (∑ a, (e (.inl a) : ℕ) + ∑ a : Fin k, (a : ℕ)) := by
  have hl' (a b) : e (.inl a) < e (.inl b) ↔ a < b := hl.lt_iff_lt
  have hr' (a b) : e (.inr a) < e (.inr b) ↔ a < b := hr.lt_iff_lt
  have h₁ (a b : Fin k) : Fin.castAdd m a < Fin.castAdd m b ↔ a < b := Iff.rfl
  have h₂ (a : Fin k) (b : Fin m) : Fin.castAdd m a < Fin.natAdd k b := by
    rw [Fin.lt_def]; simp; omega
  have h₃ {α : Type} [Preorder α] (a b : α) : ¬(a < b ∧ b < a) := fun h ↦ lt_asymm h.1 h.2
  -- The only inversions are pairs `(inl a, inr b)` with `e (inr b) < e (inl a)`.
  -- For each `a`, the number of such `b` is the position of `e (inl a)` minus `a`.
  have hcount (a : Fin k) : #{b | e (.inr b) < e (.inl a)} + a = (e (.inl a) : ℕ) := by
    rw [← Fin.card_Iio, ← Fin.card_Iio (e _), ← filter_gt_eq_Iio, ← filter_gt_eq_Iio]
    simp only [card_filter, ← e.sum_comp (fun x ↦ ite _ _ _), Fintype.sum_sum_type, hl']
    ring
  set E := finSumFinEquiv.trans (finCongr h)
  rw [sign_eq_prod_ite, ← E.prod_comp]
  simp_rw [← E.prod_comp (fun x ↦ ite _ _ _)]
  have hprod :
      (∏ x : Fin k ⊕ Fin m, ∏ i : Fin k ⊕ Fin m,
          if E i < E x ∧ (E.symm.trans e) (E x) < (E.symm.trans e) (E i) then (-1 : ℤˣ) else 1) =
        ∏ x : Fin m, ∏ y : Fin k,
          if e (Sum.inr x) < e (Sum.inl y) then (-1 : ℤˣ) else 1 := by
    simp [Fintype.prod_sum_type, E, hl', hr', h₁, h₂, (h₂ _ _).not_gt, h₃]
  rw [hprod, prod_comm, ← sum_congr rfl fun a _ ↦ hcount a, sum_add_distrib, add_assoc,
    ← two_mul, pow_add, pow_mul]
  simp [prod_ite, prod_pow_eq_pow_sum]

end Equiv.Perm

namespace Matrix

variable {R : Type*} [CommRing R]

/-- Reindexing the rows and columns of a determinant by two different equivalences multiplies the
determinant by the sign of the permutation relating them. -/
theorem det_submatrix_equiv {n α : Type*} [Fintype n] [DecidableEq n] [Fintype α]
    [DecidableEq α] (A : Matrix n n R) (e f : α ≃ n) :
    (A.submatrix e f).det = Perm.sign (f.symm.trans e) * A.det := by
  -- `A.submatrix e f = (A.submatrix f f).submatrix (f.symm.trans e) id`, so `det_permute` applies.
  rw [← det_permute, ← det_submatrix_equiv_self f]
  congr 1
  ext
  simp

/-- The sign of the shuffle that lists `I` followed by its complement. -/
private theorem sign_finSumComplEquiv {n k : ℕ} (I : Finset (Fin n)) (hI : #I = k)
    (hI' : #Iᶜ = n - k) (h : k + (n - k) = n) :
    Perm.sign ((finSumFinEquiv.trans (finCongr h)).symm.trans (finSumEquivOfFinset hI hI')) =
      (-1) ^ (∑ i ∈ I, (i : ℕ) + ∑ a : Fin k, (a : ℕ)) := by
  rw [Equiv.Perm.sign_shuffle h (finSumEquivOfFinset hI hI') (I.orderEmbOfFin hI).strictMono
    (Iᶜ.orderEmbOfFin hI').strictMono]
  simp only [finSumEquivOfFinset_inl]
  conv_rhs => rw [← I.map_orderEmbOfFin_univ hI, sum_map]
  rfl

/-- **Jacobi's complementary minor theorem.**  For `#I = #J = k`, the product of the determinant of
`A` and the complementary minor of the adjugate, with rows `Jᶜ` and columns `Iᶜ`, is
`(-1) ^ (∑ I + ∑ J)` times `(det A) ^ (n - k)` times the minor `A[I, J]`. -/
theorem det_mul_det_submatrix_adjugate {n k : ℕ} (A : Matrix (Fin n) (Fin n) R)
    {I J : Finset (Fin n)} (hI : #I = k) (hJ : #J = k) :
    A.det * ((adjugate A).submatrix
        (Jᶜ.orderEmbOfFin (k := n - k) (by rw [card_compl, Fintype.card_fin, hJ]))
        (Iᶜ.orderEmbOfFin (k := n - k) (by rw [card_compl, Fintype.card_fin, hI]))).det =
      (-1) ^ (∑ i ∈ I, (i : ℕ) + ∑ j ∈ J, (j : ℕ)) * A.det ^ (n - k) *
        (A.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  set ε : R := (-1) ^ (∑ i ∈ I, (i : ℕ) + ∑ j ∈ J, (j : ℕ))
  have hI' : #Iᶜ = n - k := by rw [card_compl, Fintype.card_fin, hI]
  have hJ' : #Jᶜ = n - k := by rw [card_compl, Fintype.card_fin, hJ]
  set P := finSumEquivOfFinset hI hI'
  set Q := finSumEquivOfFinset hJ hJ'
  set B := A.submatrix P Q
  set C := (adjugate A).submatrix Q P
  -- Reorder the rows as `I, Iᶜ` and the columns as `J, Jᶜ`; then `B * C = det A • 1` blockwise.
  have hBC : B * C = fromBlocks (A.det • 1) 0 0 (A.det • 1) := by
    ext (i | i) (j | j) <;> simp [B, C, mul_adjugate, one_apply]
  rw [← fromBlocks_toBlocks B, ← fromBlocks_toBlocks C, fromBlocks_multiply,
    fromBlocks_inj] at hBC
  -- Replace the first block column of `C` by `(1, 0)`: the upper-right block of `B * C` is zero
  -- and the lower-right block is `det A • 1`, so the product is block lower triangular.
  have hBM : B * fromBlocks 1 C.toBlocks₁₂ 0 C.toBlocks₂₂ =
      fromBlocks B.toBlocks₁₁ 0 B.toBlocks₂₁ (A.det • 1) := by
    rw [← fromBlocks_toBlocks B, fromBlocks_multiply]
    simp [hBC.2.1, hBC.2.2.2]
  -- The relative sign of the two shuffles is the sign of each shuffle; both are powers of `-1`.
  have hsign : (Perm.sign (Q.symm.trans P) : R) = ε := by
    have hk : k ≤ n := by simpa [hI] using I.card_le_univ
    have h : k + (n - k) = n := Nat.add_sub_of_le hk
    set E := finSumFinEquiv.trans (finCongr h)
    -- Conjugate both shuffles by the standard shuffle `E`, so that `sign_shuffle` applies to each.
    rw [show Q.symm.trans P = (E.symm.trans Q).symm.trans (E.symm.trans P) by ext; simp,
      Perm.sign_trans, Perm.sign_symm, sign_finSumComplEquiv I hI hI' h,
      sign_finSumComplEquiv J hJ hJ' h, ← pow_add,
      -- The two shuffle signs contribute `∑ I + ∑ J + 2 * ∑ a`; the last term is even.
      show _ + _ + (_ + _) = ∑ i ∈ I, (i : ℕ) + ∑ j ∈ J, (j : ℕ) + 2 * ∑ a : Fin k, (a : ℕ) by
        ring,
      pow_add, pow_mul]
    simp [ε]
  have hdet := congrArg det hBM
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_smul, det_submatrix_equiv,
    hsign] at hdet
  simp only [det_one, one_mul, mul_one, Fintype.card_fin] at hdet
  have hε : ε ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  -- `C.toBlocks₂₂` is `adj A[Jᶜ, Iᶜ]` and `B.toBlocks₁₁` is `A[I, J]` by definition.
  change A.det * C.toBlocks₂₂.det = ε * A.det ^ (n - k) * B.toBlocks₁₁.det
  -- Multiply `hdet` by `ε` and use `ε ^ 2 = 1`; this avoids dividing by `det A`.
  linear_combination ε * hdet - A.det * C.toBlocks₂₂.det * hε

end Matrix
