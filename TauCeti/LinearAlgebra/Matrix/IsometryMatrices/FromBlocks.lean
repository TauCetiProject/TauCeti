/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Block
public import TauCeti.LinearAlgebra.Matrix.IsometryMatrices.Basic
import TauCeti.Algebra.Polynomial.Semiconj
import TauCeti.LinearAlgebra.Matrix.Transpose
import TauCeti.RingTheory.Nilpotent.Sqrt

/-!
# Matrices preserving a block diagonal Gram matrix with a nilpotent block

Let `R` be a commutative ring in which `2` is a unit, let `A` be a symmetric matrix with unit
determinant, and let `B` be a symmetric matrix whose entries lie in a nilpotent ideal `I`. This
file counts the matrices preserving the block diagonal Gram matrix `A ⊕ B = fromBlocks A 0 0 B`:

```text
#O(A ⊕ B) = #M_{κ × ι}(R) · #O(A) · #O(B),
```

where `O(G)` denotes the matrices `X` with `Xᵀ G X = G`. Over `R = ℤ/pʳ` with `p` odd this is the
step that splits off the unimodular Jordan constituent of a `ℤ_p`-lattice in the computation of
its local density.

Write `X = fromBlocks Y₁ Y₂ Z₁ Z₂`. The equation `Xᵀ (A ⊕ B) X = A ⊕ B` says
`Y₁ᵀ A Y₁ = A - Z₁ᵀ B Z₁`, `Y₁ᵀ A Y₂ + Z₁ᵀ B Z₂ = 0` and `Y₂ᵀ A Y₂ + Z₂ᵀ B Z₂ = B`. The block `Z₁`
is arbitrary. Given `Z₁`, the first equation is solved by `Y₁`, the second determines `Y₂`, and
the third becomes an equation `Z₂ᵀ B' Z₂ = B` for `Z₂` alone. The twisted Gram matrices
`A - Z₁ᵀ B Z₁ = A (1 + M)` and `B' = B (1 + N)` differ from `A` and `B` by nilpotent `M` and `N`
that are self-adjoint for `A` and `B`. Since `2` is a unit, `1 + M` has a square root `W` which
is a polynomial in `M` (`IsNilpotent.exists_aeval_sq_eq_one_add`), so `Wᵀ A W = A (1 + M)`.
Hence the twisted Gram matrices are congruent to `A` and `B`, and the equations for `Y₁` and `Z₂`
have as many solutions as `O(A)` and `O(B)`.

## Main results

* `Matrix.exists_isUnit_det_transpose_mul_mul_eq_mul_one_add`: if `2` is a unit, `M` is nilpotent
  and `A * M = Mᵀ * A`, then `A * (1 + M)` is congruent to `A`.
* `Matrix.natCard_isometryMatrices_fromBlocks_of_isNilpotent`: the count of the matrices
  preserving `fromBlocks A 0 0 B`.

## References

* Y. Kitaoka, *Arithmetic of Quadratic Forms*, Cambridge Tracts in Mathematics 106 (1993),
  Chapter 5, for the reduction of local densities along a Jordan splitting.
-/

public section

open Polynomial

namespace Matrix

variable {n ι κ R : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] [CommRing R]

/-- **Twisting a Gram matrix by a nilpotent self-adjoint matrix.** If `2` is a unit, `M` is
nilpotent and self-adjoint for `A` in the sense that `A * M = Mᵀ * A`, then `A * (1 + M)` is
congruent to `A`: it is `Wᵀ * A * W` for a `W` with unit determinant, a square root of `1 + M`. -/
theorem exists_isUnit_det_transpose_mul_mul_eq_mul_one_add (h2 : IsUnit (2 : R))
    {A M : Matrix n n R} (hM : IsNilpotent M) (hAM : A * M = Mᵀ * A) :
    ∃ W : Matrix n n R, IsUnit W.det ∧ Wᵀ * A * W = A * (1 + M) := by
  obtain ⟨q, hq⟩ := hM.exists_aeval_sq_eq_one_add h2
  refine ⟨aeval M q, ?_, ?_⟩
  · have h := (isUnit_iff_isUnit_det _).mp (hq ▸ hM.isUnit_one_add)
    rwa [det_pow, isUnit_pow_iff two_ne_zero] at h
  · have hq' : SemiconjBy A (aeval M q) (aeval Mᵀ q) := by
      simpa only [aeval_eq_smeval] using SemiconjBy.smeval_right hAM q
    rw [← aeval_transpose, ← hq'.eq, Matrix.mul_assoc, ← sq, hq]

section FromBlocks

variable {A : Matrix ι ι R} {B : Matrix κ κ R}

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
/-- The twisted Gram matrix `A - Zᵀ B Z` is symmetric when `A` and `B` are. -/
private theorem transpose_sub_transpose_mul_mul (hA : Aᵀ = A) (hB : Bᵀ = B) (Z : Matrix κ ι R) :
    (A - Zᵀ * B * Z)ᵀ = A - Zᵀ * B * Z := by
  rw [transpose_sub, transpose_mul, transpose_mul, transpose_transpose, hA, hB, Matrix.mul_assoc]

/-- The equation `Xᵀ (A ⊕ B) X = A ⊕ B` in blocks; its lower left block is the transpose of the
upper right one. -/
private theorem fromBlocks_mem_isometryMatrices_fromBlocks_iff (hA : Aᵀ = A) (hB : Bᵀ = B)
    {Y₁ : Matrix ι ι R} {Y₂ : Matrix ι κ R} {Z₁ : Matrix κ ι R} {Z₂ : Matrix κ κ R} :
    fromBlocks Y₁ Y₂ Z₁ Z₂ ∈ isometryMatrices (fromBlocks A 0 0 B) ↔
      Y₁ᵀ * A * Y₁ + Z₁ᵀ * B * Z₁ = A ∧ Y₁ᵀ * A * Y₂ + Z₁ᵀ * B * Z₂ = 0 ∧
        Y₂ᵀ * A * Y₂ + Z₂ᵀ * B * Z₂ = B := by
  rw [mem_isometryMatrices, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj]
  simp only [Matrix.mul_zero, add_zero, zero_add]
  refine ⟨fun h => ⟨h.1, h.2.1, h.2.2.2⟩, fun ⟨h₁, h₂, h₄⟩ => ⟨h₁, h₂, ?_, h₄⟩⟩
  have h := congrArg transpose h₂
  simpa only [transpose_add, transpose_mul, transpose_transpose, transpose_zero, hA, hB,
    Matrix.mul_assoc] using h

/-- Substituting the solution `Y₂` of the off-diagonal equation into the lower right one. -/
private theorem transpose_mul_mul_add_eq (hB : Bᵀ = B) {C : Matrix ι ι R} (hC : IsUnit C.det)
    (hCt : Cᵀ = C) {Y₁ : Matrix ι ι R} (hY₁ : Y₁ᵀ * A * Y₁ = C) (Z₁ : Matrix κ ι R)
    (Z₂ : Matrix κ κ R) :
    (-(Y₁ * C⁻¹ * (Z₁ᵀ * B * Z₂)))ᵀ * A * -(Y₁ * C⁻¹ * (Z₁ᵀ * B * Z₂)) + Z₂ᵀ * B * Z₂ =
      Z₂ᵀ * (B * (1 + Z₁ * C⁻¹ * Z₁ᵀ * B)) * Z₂ := by
  calc _ = (Z₁ᵀ * B * Z₂)ᵀ * C⁻¹ᵀ * (Y₁ᵀ * A * Y₁) * C⁻¹ * (Z₁ᵀ * B * Z₂) + Z₂ᵀ * B * Z₂ := by
        simp only [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg, transpose_mul,
          Matrix.mul_assoc]
    _ = _ := by
        rw [hY₁, transpose_nonsing_inv, hCt, Matrix.mul_assoc _ C⁻¹ C, nonsing_inv_mul C hC,
          Matrix.mul_one]
        simp only [transpose_mul, transpose_transpose, hB, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_one, Matrix.mul_assoc]
        abel

/-- The equation `Xᵀ (A ⊕ B) X = A ⊕ B` solved for the blocks of `X`, given its lower left block
`Z₁`: with `C = A - Z₁ᵀ B Z₁`, it says `Y₁ᵀ A Y₁ = C`, that `Y₂` is determined by `Y₁` and `Z₂`,
and `Z₂ᵀ B (1 + Z₁ C⁻¹ Z₁ᵀ B) Z₂ = B`. -/
private theorem fromBlocks_mem_isometryMatrices_fromBlocks_iff' (hA : Aᵀ = A) (hB : Bᵀ = B)
    {Z₁ : Matrix κ ι R} (hC : IsUnit (A - Z₁ᵀ * B * Z₁).det) {Y₁ : Matrix ι ι R}
    {Y₂ : Matrix ι κ R} {Z₂ : Matrix κ κ R} :
    fromBlocks Y₁ Y₂ Z₁ Z₂ ∈ isometryMatrices (fromBlocks A 0 0 B) ↔
      Y₁ᵀ * A * Y₁ = A - Z₁ᵀ * B * Z₁ ∧
        Y₂ = -(Y₁ * (A - Z₁ᵀ * B * Z₁)⁻¹ * (Z₁ᵀ * B * Z₂)) ∧
        Z₂ᵀ * (B * (1 + Z₁ * (A - Z₁ᵀ * B * Z₁)⁻¹ * Z₁ᵀ * B)) * Z₂ = B := by
  have hCt := transpose_sub_transpose_mul_mul hA hB Z₁
  rw [fromBlocks_mem_isometryMatrices_fromBlocks_iff hA hB]
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    have hY₁ := eq_sub_of_add_eq h₁
    have hY₂ := (transpose_mul_mul_add_eq_zero_iff hC hY₁).mp h₂
    refine ⟨hY₁, hY₂, ?_⟩
    rw [← transpose_mul_mul_add_eq hB hC hCt hY₁, ← hY₂]
    exact h₃
  · rintro ⟨hY₁, hY₂, hZ₂⟩
    refine ⟨by rw [hY₁, sub_add_cancel], (transpose_mul_mul_add_eq_zero_iff hC hY₁).mpr hY₂, ?_⟩
    rw [hY₂, transpose_mul_mul_add_eq hB hC hCt hY₁]
    exact hZ₂

/-- The matrices preserving `A ⊕ B` with a given lower left block `Z`, as pairs of solutions of
the two equations of `fromBlocks_mem_isometryMatrices_fromBlocks_iff'`. -/
private noncomputable def isometryMatricesFromBlocksFiberEquiv (hA : Aᵀ = A) (hB : Bᵀ = B)
    (Z : Matrix κ ι R) (hC : IsUnit (A - Zᵀ * B * Z).det) :
    {X : isometryMatrices (fromBlocks A 0 0 B) // X.1.toBlocks₂₁ = Z} ≃
      {Y : Matrix ι ι R // Yᵀ * A * Y = A - Zᵀ * B * Z} ×
        {V : Matrix κ κ R // Vᵀ * (B * (1 + Z * (A - Zᵀ * B * Z)⁻¹ * Zᵀ * B)) * V = B} :=
  have hmem (X : {X : isometryMatrices (fromBlocks A 0 0 B) // X.1.toBlocks₂₁ = Z}) :=
    (fromBlocks_mem_isometryMatrices_fromBlocks_iff' hA hB hC).mp <| by
      have h := X.1.2
      rwa [← fromBlocks_toBlocks X.1.1, X.2] at h
  { toFun X := (⟨X.1.1.toBlocks₁₁, (hmem X).1⟩, ⟨X.1.1.toBlocks₂₂, (hmem X).2.2⟩)
    invFun YV := ⟨⟨fromBlocks YV.1.1 (-(YV.1.1 * (A - Zᵀ * B * Z)⁻¹ * (Zᵀ * B * YV.2.1))) Z
        YV.2.1, (fromBlocks_mem_isometryMatrices_fromBlocks_iff' hA hB hC).mpr
          ⟨YV.1.2, rfl, YV.2.2⟩⟩, toBlocks_fromBlocks₂₁ _ _ _ _⟩
    left_inv X := by
      refine Subtype.ext (Subtype.ext ?_)
      dsimp only
      conv_rhs => rw [← fromBlocks_toBlocks X.1.1]
      rw [X.2, ← (hmem X).2.1]
    right_inv YV := Prod.ext (Subtype.ext (toBlocks_fromBlocks₁₁ _ _ _ _))
      (Subtype.ext (toBlocks_fromBlocks₂₂ _ _ _ _)) }

omit [DecidableEq κ] in
/-- The twisted Gram matrix `A - Zᵀ B Z = A (1 - A⁻¹ Zᵀ B Z)` is congruent to `A`. -/
private theorem exists_isUnit_det_transpose_mul_mul_eq_sub (h2 : IsUnit (2 : R)) {I : Ideal R}
    (hI : IsNilpotent I) (hA : Aᵀ = A) (hdet : IsUnit A.det) (hB : Bᵀ = B)
    (hBI : ∀ i j, B i j ∈ I) (Z : Matrix κ ι R) :
    ∃ W : Matrix ι ι R, IsUnit W.det ∧ Wᵀ * A * W = A - Zᵀ * B * Z := by
  have hAinv : A⁻¹ᵀ = A⁻¹ := by rw [transpose_nonsing_inv, hA]
  have hAA : A * (A⁻¹ * (Zᵀ * (B * Z))) = Zᵀ * (B * Z) :=
    mul_nonsing_inv_cancel_left A _ hdet
  obtain ⟨W, hWdet, hWA⟩ := exists_isUnit_det_transpose_mul_mul_eq_mul_one_add h2 (A := A)
    (M := -(A⁻¹ * Zᵀ * B * Z))
    (isNilpotent_of_forall_apply_mem hI fun i j => neg_mem (mul_mul_apply_mem hBI _ _ i j))
    (by simp only [Matrix.mul_neg, Matrix.neg_mul, transpose_neg, transpose_mul,
          transpose_transpose, hB, hAinv, Matrix.mul_assoc, hAA, nonsing_inv_mul A hdet,
          Matrix.mul_one])
  refine ⟨W, hWdet, ?_⟩
  rw [hWA, Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, ← sub_eq_add_neg]
  simp only [Matrix.mul_assoc, hAA]

/-- The twisted Gram matrix `B (1 + Z C⁻¹ Zᵀ B)`, for `C = A - Zᵀ B Z`, is congruent to `B`. -/
private theorem exists_isUnit_det_transpose_mul_mul_eq_twist (h2 : IsUnit (2 : R))
    {I : Ideal R} (hI : IsNilpotent I) (hA : Aᵀ = A) (hB : Bᵀ = B) (hBI : ∀ i j, B i j ∈ I)
    (Z : Matrix κ ι R) : ∃ T : Matrix κ κ R, IsUnit T.det ∧
      Tᵀ * B * T = B * (1 + Z * (A - Zᵀ * B * Z)⁻¹ * Zᵀ * B) := by
  have hCinv : (A - Zᵀ * B * Z)⁻¹ᵀ = (A - Zᵀ * B * Z)⁻¹ := by
    rw [transpose_nonsing_inv, transpose_sub_transpose_mul_mul hA hB]
  exact exists_isUnit_det_transpose_mul_mul_eq_mul_one_add h2
    (isNilpotent_of_forall_apply_mem hI fun i j => (I.matrix κ).mul_mem_left _ hBI i j)
    (by rw [transpose_mul, transpose_mul, transpose_mul, transpose_transpose, hB, hCinv]
        simp only [Matrix.mul_assoc])

/-- **Counting the matrices preserving a block diagonal Gram matrix with a nilpotent block.** Let
`2` be a unit of `R`, let `A` be symmetric with unit determinant, and let `B` be symmetric with
entries in a nilpotent ideal. Then the matrices preserving `fromBlocks A 0 0 B` are in bijection
with the triples of a `κ × ι` matrix, a matrix preserving `A` and a matrix preserving `B`. When `R`
is finite, their number is `#R ^ (|ι| |κ|) · #O(A) · #O(B)`. -/
theorem natCard_isometryMatrices_fromBlocks_of_isNilpotent (h2 : IsUnit (2 : R)) {I : Ideal R}
    (hI : IsNilpotent I) (hA : Aᵀ = A) (hdet : IsUnit A.det) (hB : Bᵀ = B)
    (hBI : ∀ i j, B i j ∈ I) :
    Nat.card (isometryMatrices (fromBlocks A 0 0 B)) =
      Nat.card R ^ (Fintype.card ι * Fintype.card κ) * Nat.card (isometryMatrices A) *
        Nat.card (isometryMatrices B) := by
  choose W hWdet hWA using exists_isUnit_det_transpose_mul_mul_eq_sub h2 hI hA hdet hB hBI
  have hC (Z : Matrix κ ι R) : IsUnit (A - Zᵀ * B * Z).det := by
    rw [← hWA, det_mul, det_mul, det_transpose]
    exact ((hWdet Z).mul hdet).mul (hWdet Z)
  choose T hTdet hTB using exists_isUnit_det_transpose_mul_mul_eq_twist h2 hI hA hB hBI
  have e (Z : Matrix κ ι R) :
      {Y : Matrix ι ι R // Yᵀ * A * Y = A - Zᵀ * B * Z} ×
          {V : Matrix κ κ R // Vᵀ * (B * (1 + Z * (A - Zᵀ * B * Z)⁻¹ * Zᵀ * B)) * V = B} ≃
        isometryMatrices A × isometryMatrices B :=
    Equiv.prodCongr
      ((transposeMulMulEquiv (A := A) (P := 1) (B := A) (Q := W Z) (by simp) (hWdet Z)
        (by simp) (hWA Z)).trans
        (Equiv.subtypeEquivRight fun _ => mem_isometryMatrices.symm))
      ((transposeMulMulEquiv (A := B) (P := T Z) (B := B) (Q := 1) (hTdet Z) (by simp) (hTB Z)
        (by simp)).trans
        (Equiv.subtypeEquivRight fun _ => mem_isometryMatrices.symm))
  -- group the solutions by their lower left block
  rw [Nat.card_congr <| (Equiv.sigmaFiberEquiv fun X : isometryMatrices (fromBlocks A 0 0 B) =>
      X.1.toBlocks₂₁).symm.trans <| (Equiv.sigmaCongrRight fun Z =>
      (isometryMatricesFromBlocksFiberEquiv hA hB Z (hC Z)).trans (e Z)).trans
      (Equiv.sigmaEquivProd _ _)]
  simp only [Nat.card_prod, Nat.card_congr (of (m := κ) (n := ι) (α := R)).symm, Nat.card_fun,
    Nat.card_eq_fintype_card (α := ι), Nat.card_eq_fintype_card (α := κ), ← pow_mul]
  ring

end FromBlocks

end Matrix
