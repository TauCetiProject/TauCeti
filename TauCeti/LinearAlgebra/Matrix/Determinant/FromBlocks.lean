/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.Composition
public import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.SymplecticGroup

/-!
# Determinants of block matrices

Mathlib computes the determinant of a block triangular matrix `[[A, B], [0, D]]` or
`[[A, 0], [C, D]]` (`Matrix.det_fromBlocks_zero₂₁`, `Matrix.det_fromBlocks_zero₁₂`). This file adds
the antidiagonal case: with square blocks of size `n`, `det [[0, B], [C, 0]] = (-1)ⁿ det B det C`.
It follows by factoring `[[0, B], [C, 0]] = [[B, 0], [0, C]] * J * [[1, 0], [0, -1]]`, where the
standard symplectic matrix `J` has determinant `1`.

It also computes two block determinants in which one pair of opposite blocks has a single nonzero
entry. If the off-diagonal blocks of `[[Z, C], [C', W]]` have the single entries `c` and `c'` at
the same diagonal position `(i, i)`, splitting the two rows through these entries gives
`det Z det W - c c' adj(Z)ᵢᵢ adj(W)ᵢᵢ`. Exchanging the two block columns turns
`[[S_a, Z], [W, S_b]]`, whose diagonal blocks have single entries `a` and `b` at the last corner of
`Fin (n + 1)`, into a matrix of that shape, and the corner entries of the adjugates are the leading
principal minors of order `n`.

## Main results

* `Matrix.det_fromBlocks_zero₁₁_zero₂₂`: the determinant of an antidiagonal block matrix
  `[[0, B], [C, 0]]` with square blocks of size `n` is `(-1)ⁿ det B det C`.
* `Matrix.det_fromBlocks_single₁₂_single₂₁`: the determinant of a block matrix whose off-diagonal
  blocks each have a single entry on the diagonal.
* `Matrix.det_fromBlocks_single₁₁_single₂₂`: the determinant of a block matrix whose diagonal blocks
  each have a single entry at the last corner, in terms of the determinants and the leading
  principal minors of the off-diagonal blocks.
* `Matrix.det_comp_map_of_eq_reindex_fromBlocks_diagonal`: if every `χ c` is, up to reindexing,
  the block sum of `ψ c` and the diagonal matrix of the `η t c`, then the determinant of the block
  matrix `(χ (M i j))_{i,j}` is that of `(ψ (M i j))_{i,j}` times the determinants of the
  `(η t (M i j))_{i,j}`.

## Provenance

`Matrix.det_fromBlocks_single₁₂_single₂₁` is adapted from the Lean project grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Spanning/Bessel/Basic.lean`, declaration `New.det_fromBlocks_single`.
`Matrix.det_comp_map_of_eq_reindex_fromBlocks_diagonal` follows
`New.Selmer.det_comp_map_eq_mul_prod` in grh-lean, file
`src/New/Congruences/FirstOrder/RibetMethod.lean`.
-/

public section

namespace Matrix

variable {l R : Type*} [Fintype l] [DecidableEq l] [CommRing R]

/-- **The determinant of an antidiagonal block matrix.** With square blocks of size `n`,
`det [[0, B], [C, 0]] = (-1)ⁿ det B det C`. -/
@[simp]
theorem det_fromBlocks_zero₁₁_zero₂₂ (B C : Matrix l l R) :
    (fromBlocks 0 B C 0).det = (-1) ^ Fintype.card l * B.det * C.det := by
  -- `[[0, B], [C, 0]] = [[B, 0], [0, C]] * J * [[1, 0], [0, -1]]`, and `det J = 1`.
  have h : fromBlocks 0 B C 0 = fromBlocks B 0 0 C * (J l R * fromBlocks 1 0 0 (-1)) := by
    simp [J, fromBlocks_multiply]
  rw [h]
  simp [det_J, det_fromBlocks_zero₂₁, det_neg]
  ring

/-! ### Block matrices with single-entry blocks -/

section Block

open _root_.Fin

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **Determinant of a block matrix with single off-diagonal entries.** For square matrices `Z`,
`W` and scalars `c`, `c'`, the block matrix whose off-diagonal blocks have the single entries `c`
and `c'` at `(i, i)` has determinant `det Z * det W - c * c' * adj(Z)ᵢᵢ * adj(W)ᵢᵢ`. -/
theorem det_fromBlocks_single₁₂_single₂₁ (Z W : Matrix m m R) (i : m) (c c' : R) :
    (fromBlocks Z (single i i c) (single i i c') W).det =
      Z.det * W.det - c * c' * (Z.adjugate i i * W.adjugate i i) := by
  set C : Matrix m m R := single i i c
  set C' : Matrix m m R := single i i c'
  have h_zero (X : Matrix m m R) : (X.updateRow i 0).det = 0 :=
    det_eq_zero_of_row_eq_zero i (by simp)
  have h_minor (X : Matrix m m R) (d : R) :
      (X.updateRow i (Pi.single i d)).det = d * X.adjugate i i := by
    simp [adjugate_apply, ← det_updateRow_smul, ← Pi.single_smul']
  -- Split the row `inl i` and then the row `inr i` into its two blocks.
  have h_split_inl : (fromBlocks Z C C' W).det =
      (fromBlocks Z 0 C' W).det + (fromBlocks (Z.updateRow i 0) C C' W).det := by
    refine det_eq_add_of_row_eq_add (.inl i) (by ext (b | b) <;> simp [C, updateRow_apply]) ?_ ?_
    all_goals rintro (a | a) ha <;> ext (b | b) <;>
      simp_all [C, updateRow_apply, eq_comm]
  have h_split_inr : (fromBlocks (Z.updateRow i 0) C C' W).det =
      (fromBlocks (Z.updateRow i 0) C 0 W).det +
        (fromBlocks (Z.updateRow i 0) C C' (W.updateRow i 0)).det := by
    refine det_eq_add_of_row_eq_add (.inr i) (by ext (b | b) <;> simp [C', updateRow_apply]) ?_ ?_
    all_goals rintro (a | a) ha <;> ext (b | b) <;>
      simp_all [C', updateRow_apply, eq_comm]
  -- In the last term, exchange the two rows.
  have h_swap : fromBlocks (Z.updateRow i 0) C C' (W.updateRow i 0) =
      (fromBlocks (Z.updateRow i (Pi.single i c')) 0 0
        (W.updateRow i (Pi.single i c))).submatrix (Equiv.swap (.inl i) (.inr i)) id := by
    ext (a | a) (b | b) <;> by_cases ha : a = i <;>
      simp [C, C', updateRow_apply, single_apply, Pi.single_apply, ha, eq_comm (a := i),
        Equiv.swap_apply_of_ne_of_ne]
  rw [h_split_inl, h_split_inr, h_swap, det_permute, Equiv.Perm.sign_swap Sum.inl_ne_inr,
    det_fromBlocks_zero₁₂, det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁, h_zero, h_minor, h_minor]
  push_cast
  ring

variable {n : ℕ}

/-- **Determinant of a block matrix with single diagonal entries.** For matrices `Z`, `W` indexed
by `Fin (n + 1)` and scalars `a`, `b`, the block matrix `[[S_a, Z], [W, S_b]]`, whose diagonal
blocks have the single entries `a` and `b` at the last corner, has determinant
`(-1) ^ (n + 1) * (det Z * det W - a * b * D(Z) * D(W))`, where `D` is the leading principal
minor of order `n`. -/
theorem det_fromBlocks_single₁₁_single₂₂ (Z W : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (a b : R) :
    (fromBlocks (single (last n) (last n) a) Z W (single (last n) (last n) b)).det =
      (-1) ^ (n + 1) * (Z.det * W.det - a * b *
        ((Z.submatrix castSucc castSucc).det * (W.submatrix castSucc castSucc).det)) := by
  -- Exchanging the two block columns gives a matrix of the shape of
  -- `det_fromBlocks_single₁₂_single₂₁`.
  have h : fromBlocks (single (last n) (last n) a) Z W (single (last n) (last n) b) =
      fromBlocks Z (single (last n) (last n) a) (single (last n) (last n) b) W *
        fromBlocks 0 1 1 0 := by
    simp [fromBlocks_multiply]
  rw [h, det_mul, det_fromBlocks_zero₁₁_zero₂₂, det_fromBlocks_single₁₂_single₂₁,
    adjugate_last_last_eq_det_submatrix_castSucc, adjugate_last_last_eq_det_submatrix_castSucc]
  simp only [Fintype.card_fin, det_one, mul_one]
  ring

end Block

/-- Suppose that every matrix `χ c` is, after reindexing along `e : r ⊕ T ≃ σ`, the block sum of
`ψ c` and of the diagonal matrix of the scalars `η t c`. Then for a square matrix `M` over `A`, the
determinant of the block matrix `(χ (M i j))_{i,j}` is the determinant of `(ψ (M i j))_{i,j}` times
the product over `t` of the determinants of `(η t (M i j))_{i,j}`. -/
theorem det_comp_map_of_eq_reindex_fromBlocks_diagonal {ι r T σ A : Type*} [Fintype ι]
    [DecidableEq ι] [Fintype r] [DecidableEq r] [Fintype T] [DecidableEq T] [Fintype σ]
    [DecidableEq σ] {e : r ⊕ T ≃ σ} {χ : A → Matrix σ σ R} {ψ : A → Matrix r r R}
    {η : T → A → R} (M : Matrix ι ι A)
    (hχ : ∀ c, χ c = reindex e e (fromBlocks (ψ c) 0 0 (diagonal fun t ↦ η t c))) :
    (comp ι ι σ σ R (M.map χ)).det =
      (comp ι ι r r R (M.map ψ)).det * ∏ t, (M.map (η t)).det := by
  let e' : ι × r ⊕ ι × T ≃ ι × σ :=
    (Equiv.prodSumDistrib ι r T).symm.trans (.prodCongr (.refl ι) e)
  have h : (comp ι ι σ σ R (M.map χ)).submatrix e' e' =
      fromBlocks (comp ι ι r r R (M.map ψ)) 0 0 (blockDiagonal fun t ↦ M.map (η t)) := by
    ext1 (a | a) (b | b) <;> simp [e', hχ, blockDiagonal, diagonal]
  rw [← det_submatrix_equiv_self e', h, det_fromBlocks_zero₂₁, det_blockDiagonal]

end Matrix
