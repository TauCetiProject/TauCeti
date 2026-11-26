/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import TauCeti.LinearAlgebra.Matrix.IndefiniteUnitaryGroup
public import TauCeti.LinearAlgebra.Matrix.LDU
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Matrix.Determinant.FromBlocks

/-!
# The Gram determinant of two frames

Let `A` be the Gram matrix of a Hermitian form `⟨z, w⟩ = star z ⬝ᵥ A *ᵥ w` on `ι → R`. A *frame
of norm `-T`* is a family `F = (F₀, …, Fₙ)` of `n + 1` vectors, the columns of a matrix
`F : Matrix ι (Fin (n + 1)) R`, whose Gram matrix `Fᴴ * A * F` has the single entry `-T` at the
corner `(n, n)`: the first `n` vectors span a totally isotropic subspace orthogonal to the last
one, which has norm `-T`. For two frames `F` and `F'` of norms `-T` and `-T'`, let
`Z = Fᴴ * A * F'` be the matrix of the products `⟨F_a, F'_b⟩`, let `D` be its leading principal
minor of order `n` and put

`Gr = |det Z|² - T T' |D|²`.

Then the Gram determinant of the `2n + 2` vectors `F ∪ F'` is `(-1) ^ (n + 1) * Gr`
(`Matrix.det_conjTranspose_fromCols_mul_mul_fromCols_of_frame`). Typically `F' = x F''` for an
isometry `x` of the form and a second frame `F''`, so that `Z` is the matrix of the products
`⟨F_a, x F''_b⟩` (`Matrix.det_conjTranspose_fromCols_mul_mul_fromCols_mul_of_frame`).

The Gram matrix of `F ∪ F'` is the block matrix `[[S, Z], [Zᴴ, S']]`, whose diagonal blocks `S`
and `S'` each have one nonzero entry. Exchanging the two block columns gives
`[[Z, S], [S', Zᴴ]]`, and expanding its determinant along the two rows that meet the entries of
`S` and `S'` gives `det Z det W - c c' adj(Z)ₙₙ adj(W)ₙₙ` for a block matrix with diagonal blocks
`Z`, `W` and off-diagonal blocks with the single entries `c`, `c'`
(`Matrix.det_fromBlocks_single_single`). The corner entries of the adjugates are the leading
principal minors of order `n`.

The leading principal minors of `Z` are unchanged when `F` and `F'` are replaced by `F * U`
and `F' * U'` for upper unitriangular `U` and `U'`, that is when each frame vector is changed by
a combination of the earlier ones (`Matrix.det_submatrix_castLE_conjTranspose_mul_mul`, from
`Matrix.det_submatrix_castLE_mul_mul`). If an
isometry `s` and an invertible `s'` move the two frames in this way, the leading principal
minors of the matrix of the products `⟨F_a, s x s'⁻¹ F'_b⟩` are those of the products
`⟨F_a, x F'_b⟩` (`Matrix.det_submatrix_castLE_frame_mul_mul`); in particular so is `Gr`.

## Main results

* `Matrix.det_fromBlocks_single_single`: the determinant of a block matrix whose off-diagonal
  blocks each have a single entry on the diagonal.
* `Matrix.det_fromBlocks_single_last`: the determinant of a block matrix whose diagonal blocks
  each have a single entry at the last corner, in terms of the determinants and the leading
  principal minors of the off-diagonal blocks.
* `Matrix.det_conjTranspose_fromCols_mul_mul_fromCols_of_frame`: the Gram determinant of two frames.
* `Matrix.det_submatrix_castLE_frame_mul_mul`: invariance of the leading principal minors of the
  products of two frames under isometries moving the frames by unitriangular matrices.

## Provenance and references

The Gram determinant identity in the case `T = T'` is adapted from the Lean project grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC), file
`src/New/Spanning/Bessel/Basic.lean`, declarations `New.det_fromBlocks_single`,
`New.det_eq_add_of_row_eq_add` and `New.det_gram_framePair`; the invariance of the leading minors
follows `New.Filling.leadingMinor_frameGram_besselU_mul` in
`src/Lib/DiscreteSeries/Bruhat/FloorGroups.lean`. Here the two frames may have different norms,
and the invariance is derived from the leading block minors of block `LDU` products.

These are the algebraic parts of the big cell of `U(p, q)` relative to a Bessel subgroup, used in
the analysis of Bessel models of discrete series, compare
* W. T. Gan, B. H. Gross and D. Prasad, *Symplectic local root numbers, central critical L-values,
  and restriction problems in the representation theory of classical groups*, Astérisque 346
  (2012), Section 12, for the Bessel subgroups.
-/

public section

open Fin

namespace Matrix

/-! ### Two block determinants -/

section Block

variable {m R : Type*} [Fintype m] [DecidableEq m] [CommRing R]

/-- **Determinant of a block matrix with single off-diagonal entries.** For square matrices `Z`,
`W` and scalars `c`, `c'`, the block matrix whose off-diagonal blocks have the single entries `c`
and `c'` at `(i, i)` has determinant `det Z * det W - c * c' * adj(Z)ᵢᵢ * adj(W)ᵢᵢ`. -/
theorem det_fromBlocks_single_single (Z W : Matrix m m R) (i : m) (c c' : R) :
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
theorem det_fromBlocks_single_last (Z W : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (a b : R) :
    (fromBlocks (single (last n) (last n) a) Z W (single (last n) (last n) b)).det =
      (-1) ^ (n + 1) * (Z.det * W.det - a * b *
        ((Z.submatrix castSucc castSucc).det * (W.submatrix castSucc castSucc).det)) := by
  -- Exchanging the two block columns gives a matrix of the shape of
  -- `det_fromBlocks_single_single`.
  have h : fromBlocks (single (last n) (last n) a) Z W (single (last n) (last n) b) =
      fromBlocks Z (single (last n) (last n) a) (single (last n) (last n) b) W *
        fromBlocks 0 1 1 0 := by
    simp [fromBlocks_multiply]
  rw [h, det_mul, det_fromBlocks_zero₁₁_zero₂₂, det_fromBlocks_single_single,
    adjugate_last_last_eq_det_submatrix_castSucc, adjugate_last_last_eq_det_submatrix_castSucc]
  simp only [Fintype.card_fin, det_one, mul_one]
  ring

end Block

/-! ### The Gram determinant of two frames -/

section Frame

variable {ι R : Type*} [Fintype ι] [CommRing R] [StarRing R] {n : ℕ} {A : Matrix ι ι R}
  {F F' : Matrix ι (Fin (n + 1)) R} {T T' : R}

/-- **The Gram determinant of two frames.** Let `A` be Hermitian, and let `F` and `F'` be frames
of norms `-T` and `-T'`: the Gram matrices `Fᴴ * A * F` and `F'ᴴ * A * F'` have the single
entries `-T` and `-T'` at the last corner. With `Z = Fᴴ * A * F'` the matrix of the products
`⟨F_a, F'_b⟩` and `D` its leading principal minor of order `n`, the Gram determinant of the
`2n + 2` vectors `F ∪ F'` is `(-1) ^ (n + 1) * (|det Z|² - T T' |D|²)`, where `|x|²` is
`x * star x`. -/
theorem det_conjTranspose_fromCols_mul_mul_fromCols_of_frame (hA : A.IsHermitian)
    (hF : Fᴴ * A * F = single (last n) (last n) (-T))
    (hF' : F'ᴴ * A * F' = single (last n) (last n) (-T')) :
    ((fromCols F F')ᴴ * A * fromCols F F').det =
      (-1) ^ (n + 1) * ((Fᴴ * A * F').det * star (Fᴴ * A * F').det - T * T' *
        (((Fᴴ * A * F').submatrix castSucc castSucc).det *
          star ((Fᴴ * A * F').submatrix castSucc castSucc).det)) := by
  have h_adj : F'ᴴ * A * F = (Fᴴ * A * F')ᴴ := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]
  have h_gram : (fromCols F F')ᴴ * A * fromCols F F' =
      fromBlocks (single (last n) (last n) (-T)) (Fᴴ * A * F') (Fᴴ * A * F')ᴴ
        (single (last n) (last n) (-T')) := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul, fromRows_mul_fromCols, hF,
      hF', h_adj]
  rw [h_gram, det_fromBlocks_single_last, det_conjTranspose, ← conjTranspose_submatrix,
    det_conjTranspose, neg_mul_neg]

/-- **The Gram determinant of a frame and the image of a frame.** For an isometry `x` of the
Hermitian form `A`, that is `star x * A * x = A` as for the elements of `unitaryGroupOf A`, and
frames `F`, `F'` of norms `-T`, `-T'`, the Gram determinant of the
`2n + 2` vectors `F ∪ x F'` is `(-1) ^ (n + 1) * (|det Z|² - T T' |D|²)`, where `Z` is the matrix
of the products `⟨F_a, x F'_b⟩` and `D` its leading principal minor of order `n`. -/
theorem det_conjTranspose_fromCols_mul_mul_fromCols_mul_of_frame (hA : A.IsHermitian)
    {x : Matrix ι ι R} (hx : star x * A * x = A) (hF : Fᴴ * A * F = single (last n) (last n) (-T))
    (hF' : F'ᴴ * A * F' = single (last n) (last n) (-T')) :
    ((fromCols F (x * F'))ᴴ * A * fromCols F (x * F')).det =
      (-1) ^ (n + 1) * ((Fᴴ * A * (x * F')).det * star (Fᴴ * A * (x * F')).det - T * T' *
        (((Fᴴ * A * (x * F')).submatrix castSucc castSucc).det *
          star ((Fᴴ * A * (x * F')).submatrix castSucc castSucc).det)) :=
  det_conjTranspose_fromCols_mul_mul_fromCols_of_frame hA hF
    (by rw [conjTranspose_mul_mul_mul_of_star_mul_mul_eq hx, hF'])

end Frame

/-! ### Invariance of the leading principal minors -/

section Invariance

variable {R : Type*} [CommRing R] {n l : ℕ}

variable [StarRing R]

/-- **Leading principal minors of the products of two frames.** Replacing the frames `F` and `F'`
by `F * U` and `F' * U'` for upper unitriangular `U` and `U'`, that is changing each frame vector
by a combination of the earlier ones, does not change the leading principal minors of the matrix
`Fᴴ * A * F'` of the products `⟨F_a, F'_b⟩`. -/
theorem det_submatrix_castLE_conjTranspose_mul_mul {ι : Type*} [Fintype ι] (A : Matrix ι ι R)
    (F F' : Matrix ι (Fin n) R) {U U' : Matrix (Fin n) (Fin n) R} (hU : U.BlockUnitriangular id)
    (hU' : U'.BlockUnitriangular id) (h : l ≤ n) :
    (((F * U)ᴴ * A * (F' * U')).submatrix (castLE h) (castLE h)).det =
      ((Fᴴ * A * F').submatrix (castLE h) (castLE h)).det := by
  rw [show (F * U)ᴴ * A * (F' * U') = Uᴴ * (Fᴴ * A * F') * U' by
    simp only [conjTranspose_mul, Matrix.mul_assoc],
    det_submatrix_castLE_mul_mul hU.conjTranspose hU' h]

/-- **Invariance of the leading principal minors of two frames.** Let `s` be an isometry of the
form `A` and `s'` invertible, and suppose that `s⁻¹` and `s'⁻¹` move the frames `F` and `F'` by
upper unitriangular matrices: `s⁻¹ F = F U` and `s'⁻¹ F' = F' U'`. Then for every `x` the
leading principal minors of the matrix of the products `⟨F_a, s x s'⁻¹ F'_b⟩` are those of the
products `⟨F_a, x F'_b⟩`. -/
theorem det_submatrix_castLE_frame_mul_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι R} {s s' : GL ι R} (hs : s ∈ unitaryGroupOf A) {F F' : Matrix ι (Fin n) R}
    {U U' : Matrix (Fin n) (Fin n) R} (hU : U.BlockUnitriangular id)
    (hU' : U'.BlockUnitriangular id) (hsF : (↑s⁻¹ : Matrix ι ι R) * F = F * U)
    (hsF' : (↑s'⁻¹ : Matrix ι ι R) * F' = F' * U') (x : Matrix ι ι R) (h : l ≤ n) :
    ((Fᴴ * A * ((s : Matrix ι ι R) * x * (↑s'⁻¹ : Matrix ι ι R) * F')).submatrix (castLE h)
      (castLE h)).det =
      ((Fᴴ * A * (x * F')).submatrix (castLE h) (castLE h)).det := by
  -- `A s = (s⁻¹)ᴴ A`, since `s` preserves `A`.
  have h_form : A * s = (↑s⁻¹ : Matrix ι ι R)ᴴ * A := by
    have hs' := mem_unitaryGroupOf_iff.1 (inv_mem hs)
    calc A * s = star (↑s⁻¹ : Matrix ι ι R) * A * (↑(s⁻¹ * s) : Matrix ι ι R) := by
          rw [Units.val_mul, ← Matrix.mul_assoc, hs']
      _ = _ := by rw [inv_mul_cancel, Units.val_one, Matrix.mul_one, star_eq_conjTranspose]
  have h_eq : Fᴴ * A * ((s : Matrix ι ι R) * x * (↑s'⁻¹ : Matrix ι ι R) * F') =
      (F * U)ᴴ * (A * x) * (F' * U') := by
    calc _ = Fᴴ * (A * (s : Matrix ι ι R)) * x * ((↑s'⁻¹ : Matrix ι ι R) * F') := by
          simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [h_form, hsF', ← hsF, conjTranspose_mul]
        simp only [Matrix.mul_assoc]
  rw [h_eq, det_submatrix_castLE_conjTranspose_mul_mul _ _ _ hU hU' h]
  simp only [Matrix.mul_assoc]

end Invariance

end Matrix
