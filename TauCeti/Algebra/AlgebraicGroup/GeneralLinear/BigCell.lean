/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.LDU
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Coordinates of the block big cell

For a ranking `b` of a finite matrix index type, the block big cell is the principal open
subset of matrix space on which all leading block minors are invertible. Its coordinate
algebra is the polynomial ring in the matrix entries localized at the product of those
minors. The largest leading block is the whole matrix, so this open lies in the general
linear group, including over arbitrary commutative rings.

`TauCeti.GeneralLinear.blockBigCellPointsEquiv` identifies algebra maps from this coordinate
algebra with matrices having unit leading block minors. The universal matrix admits a block
`LDU` factorization **in the coordinate algebra itself**. Consequently its factors have
entries regular on this principal open, not merely pointwise factorizations over fields.
`TauCeti.GeneralLinear.exists_blockBigCell_universal_factors` proves that evaluating these
same three matrices recovers the unique factors of every point, over every coefficient
algebra. No assertion about a Chevalley subgroup's intersection with this open is made here.

The factorization input is `Matrix.exists_blockLDU_iff` and its uniqueness theorem
`Matrix.eq_of_blockLDU_eq`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, II.1.
-/

public section

namespace TauCeti.GeneralLinear

open Matrix OrderDual

variable {n α : Type*} [Fintype n] [DecidableEq n] [LinearOrder α]
variable (R : Type*) [CommRing R] (b : n → α)

/-- The product of the leading block minors of the generic matrix. Repeated ranks only
repeat factors, which does not change the principal open. -/
noncomputable def blockBigCellDenominator : MvPolynomial (n × n) R :=
  ∏ i, ((Matrix.mvPolynomialX n n R).toSquareBlockProp fun j => b j ≤ b i).det

/-- The coordinate algebra of the block big cell, localized at the product of its leading
block minors. -/
abbrev BlockBigCellCoordinateAlgebra :=
  Localization.Away (blockBigCellDenominator R b)

/-- The universal matrix on the block big cell. -/
noncomputable def blockBigCellMatrix : Matrix n n (BlockBigCellCoordinateAlgebra R b) :=
  (Matrix.mvPolynomialX n n R).map (algebraMap _ _)

variable {R} {b}

/-- Each leading block minor of the universal matrix is invertible. -/
theorem isUnit_blockBigCellMatrix_minor (i : n) :
    IsUnit ((blockBigCellMatrix R b).toSquareBlockProp fun j => b j ≤ b i).det := by
  have h := IsLocalization.Away.isUnit_of_dvd
    (S := BlockBigCellCoordinateAlgebra R b) (blockBigCellDenominator R b)
    (Finset.dvd_prod_of_mem
      (fun k => ((Matrix.mvPolynomialX n n R).toSquareBlockProp fun j => b j ≤ b k).det)
      (Finset.mem_univ i))
  rw [blockBigCellMatrix, Matrix.toSquareBlockProp_map, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  exact h

/-- The block big cell is contained in the general linear group over any base ring. -/
theorem isUnit_det_blockBigCellMatrix : IsUnit (blockBigCellMatrix R b).det := by
  obtain ⟨L, D, U, hL, _, _, hU, hD, h⟩ :=
    (Matrix.exists_blockLDU_iff (blockBigCellMatrix R b)).mp
      isUnit_blockBigCellMatrix_minor
  rw [h, Matrix.det_mul, Matrix.det_mul, hL.det_eq_one, hU.det_eq_one, one_mul, mul_one]
  exact hD

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Evaluating the denominator gives the product of the leading block minors. -/
@[simp]
theorem aeval_blockBigCellDenominator (M : Matrix n n S) :
    MvPolynomial.aeval (fun ij : n × n => M ij.1 ij.2) (blockBigCellDenominator R b) =
      ∏ i, (M.toSquareBlockProp fun j => b j ≤ b i).det := by
  simp only [blockBigCellDenominator, map_prod, AlgHom.map_det,
    AlgHom.mapMatrix_apply]
  congr 1
  funext i
  rw [← Matrix.toSquareBlockProp_map]
  congr 2
  ext j k
  simp [Matrix.mvPolynomialX]

/-- Evaluation at a matrix whose leading block minors are units. -/
noncomputable def blockBigCellEval (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) :
    BlockBigCellCoordinateAlgebra R b →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (blockBigCellDenominator R b)
    (f := MvPolynomial.aeval (fun ij : n × n => M ij.1 ij.2))
    (by simpa only [aeval_blockBigCellDenominator] using IsUnit.prod_univ_iff.mpr hM)

/-- Evaluation of a localized polynomial agrees with polynomial evaluation. -/
@[simp]
theorem blockBigCellEval_algebraMap (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det)
    (p : MvPolynomial (n × n) R) :
    blockBigCellEval (R := R) M hM (algebraMap _ _ p) =
      MvPolynomial.aeval (fun ij : n × n => M ij.1 ij.2) p := by
  simp [blockBigCellEval]

/-- Evaluation recovers the matrix represented by the point. -/
@[simp]
theorem map_blockBigCellMatrix (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) :
    (blockBigCellMatrix R b).map (blockBigCellEval M hM) = M := by
  ext i j
  simp [blockBigCellMatrix, Matrix.mvPolynomialX]

/-- Algebra maps out of the block big cell are determined by the universal matrix entries. -/
theorem blockBigCell_algHom_ext {f g : BlockBigCellCoordinateAlgebra R b →ₐ[R] S}
    (h : (blockBigCellMatrix R b).map f = (blockBigCellMatrix R b).map g) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (blockBigCellDenominator R b))
  apply MvPolynomial.algHom_ext
  intro ij
  exact congrFun (congrFun h ij.1) ij.2

/-- Every algebra-valued point of the block big cell has invertible leading block minors. -/
theorem isUnit_minor_map_blockBigCellMatrix
    (f : BlockBigCellCoordinateAlgebra R b →ₐ[R] S) (i : n) :
    IsUnit (((blockBigCellMatrix R b).map f).toSquareBlockProp fun j => b j ≤ b i).det := by
  rw [Matrix.toSquareBlockProp_map, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
  exact (isUnit_blockBigCellMatrix_minor (R := R) (b := b) i).map f

variable (R b S) in
/-- The block big cell represents matrices with invertible leading block minors, over every
commutative coefficient algebra. -/
noncomputable def blockBigCellPointsEquiv :
    (BlockBigCellCoordinateAlgebra R b →ₐ[R] S) ≃
      {M : Matrix n n S // ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det} where
  toFun f := ⟨(blockBigCellMatrix R b).map f, isUnit_minor_map_blockBigCellMatrix f⟩
  invFun M := blockBigCellEval M.val M.property
  left_inv f := blockBigCell_algHom_ext
    (map_blockBigCellMatrix _ (isUnit_minor_map_blockBigCellMatrix f))
  right_inv M := Subtype.ext (map_blockBigCellMatrix M.val M.property)

/-- The represented matrix of an algebra-valued point is obtained by mapping the universal
matrix entrywise. -/
@[simp]
theorem blockBigCellPointsEquiv_apply (f : BlockBigCellCoordinateAlgebra R b →ₐ[R] S) :
    (blockBigCellPointsEquiv R b S f).val = (blockBigCellMatrix R b).map f :=
  (rfl)

/-- The inverse of the point equivalence is evaluation. -/
@[simp]
theorem blockBigCellPointsEquiv_symm_apply
    (M : {M : Matrix n n S // ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det}) :
    (blockBigCellPointsEquiv R b S).symm M = blockBigCellEval M.val M.property :=
  (rfl)

/-- Evaluation is natural in the coefficient algebra. -/
theorem blockBigCellEval_comp {T : Type*} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) :
    f.comp (blockBigCellEval M hM) = blockBigCellEval (M.map f)
      (fun i => by
        rw [Matrix.toSquareBlockProp_map, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
        exact (hM i).map f) := by
  apply blockBigCell_algHom_ext
  rw [AlgHom.coe_comp, ← Matrix.map_map, map_blockBigCellMatrix, map_blockBigCellMatrix]

variable (R b)

/-- The block `LDU` factors are regular on the big cell: there are three matrices over its
coordinate algebra whose evaluations are the unique factors of every algebra-valued point.
The diagonal factor is invertible in the coordinate algebra, not merely at field-valued points. -/
theorem exists_blockBigCell_universal_factors :
    ∃ L D U : Matrix n n (BlockBigCellCoordinateAlgebra R b),
      L.BlockUnitriangular (toDual ∘ b) ∧ D.BlockTriangular b ∧
      D.BlockTriangular (toDual ∘ b) ∧ U.BlockUnitriangular b ∧ IsUnit D.det ∧
      blockBigCellMatrix R b = L * D * U ∧
      ∀ (S : Type*) [CommRing S] [Algebra R S] (M : Matrix n n S)
        (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det)
        (L' D' U' : Matrix n n S),
        L'.BlockUnitriangular (toDual ∘ b) → D'.BlockTriangular b →
        D'.BlockTriangular (toDual ∘ b) → U'.BlockUnitriangular b →
        M = L' * D' * U' →
        L.map (blockBigCellEval M hM) = L' ∧
        D.map (blockBigCellEval M hM) = D' ∧ U.map (blockBigCellEval M hM) = U' := by
  obtain ⟨L, D, U, hL, hD, hD₁, hU, hdet, h⟩ :=
    (Matrix.exists_blockLDU_iff (blockBigCellMatrix R b)).mp
      isUnit_blockBigCellMatrix_minor
  refine ⟨L, D, U, hL, hD, hD₁, hU, hdet, h, ?_⟩
  intro S _ _ M hM L' D' U' hL' hD' hD'₁ hU' h'
  let f := blockBigCellEval (R := R) M hM
  apply Matrix.eq_of_blockLDU_eq (hL.map f) (hD.map f) (hD₁.map f) (hU.map f)
    hL' hD' hD'₁ hU'
  · simpa only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det] using hdet.map f
  · rw [← Matrix.map_mul, ← Matrix.map_mul, ← h, map_blockBigCellMatrix, h']

end TauCeti.GeneralLinear
