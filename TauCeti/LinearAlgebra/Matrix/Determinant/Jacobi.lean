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
public import TauCeti.GroupTheory.Perm.Inversion

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
the cofactor formula for an entry of the adjugate multiplied by `det A`; when `det A` is a unit,
this recovers the usual cofactor formula.

## Main results

* `Matrix.det_mul_det_submatrix_adjugate`: Jacobi's complementary minor theorem in adjugate form.
-/

public section

open Equiv Finset

namespace Matrix

variable {R : Type*} [CommRing R]

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
  have hC : C.toBlocks₂₂ =
      (adjugate A).submatrix (Jᶜ.orderEmbOfFin (k := n - k) hJ')
        (Iᶜ.orderEmbOfFin (k := n - k) hI') := by
    ext i j
    simp [C, toBlocks₂₂, P, Q]
  have hB₁₁ : B.toBlocks₁₁ = A.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ) := by
    ext i j
    simp [B, toBlocks₁₁, P, Q]
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
    -- Conjugate both shuffles by the standard shuffle `E`, so that the shuffle-sign lemma applies
    -- to each.
    rw [show Q.symm.trans P = (E.symm.trans Q).symm.trans (E.symm.trans P) by ext; simp,
      Perm.sign_trans, Perm.sign_symm, TauCeti.sign_finSumEquivOfFinset I hI,
      TauCeti.sign_finSumEquivOfFinset J hJ, ← pow_add,
      -- The two shuffle signs contribute `∑ I + ∑ J + 2 * ∑ a`; the last term is even.
      show _ + _ + (_ + _) = ∑ i ∈ I, (i : ℕ) + ∑ j ∈ J, (j : ℕ) + 2 * ∑ a : Fin k, (a : ℕ) by
        ring,
      pow_add, pow_mul]
    simp [ε]
  have hdet := congrArg det hBM
  have hB : B.det = (A.reindex P.symm Q.symm).det := by simp [B, reindex_apply]
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, det_smul, hB, det_reindex,
    Equiv.symm_symm, hsign] at hdet
  simp only [det_one, one_mul, mul_one, Fintype.card_fin] at hdet
  have hε : ε ^ 2 = 1 := by rw [← pow_mul, pow_mul', neg_one_sq, one_pow]
  -- Rewrite the complementary minor and the original minor as the corresponding blocks.
  rw [← hC, ← hB₁₁]
  -- Multiply `hdet` by `ε` and use `ε ^ 2 = 1`; this avoids dividing by `det A`.
  linear_combination ε * hdet - A.det * C.toBlocks₂₂.det * hε

end Matrix
