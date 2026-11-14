/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.LDU
public import TauCeti.LinearAlgebra.Matrix.MvPolynomial
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
`TauCeti.GeneralLinear.blockBigCellLower`, `TauCeti.GeneralLinear.blockBigCellDiag`, and
`TauCeti.GeneralLinear.blockBigCellUpper` name these factors. Their `map_blockBigCellLower`,
`map_blockBigCellDiag`, and `map_blockBigCellUpper` lemmas show that evaluation recovers the
unique factors of every point, over every coefficient algebra. No assertion about a Chevalley
subgroup's intersection with this open is made here.

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

/-- The entries of the universal matrix are the localized coordinate variables. -/
@[simp]
theorem blockBigCellMatrix_apply (i j : n) :
    blockBigCellMatrix R b i j =
      algebraMap (MvPolynomial (n × n) R) _ (MvPolynomial.X (i, j)) :=
  (rfl)

variable {R} {b}

/-- Each leading block minor of the universal matrix is invertible. -/
theorem isUnit_det_toSquareBlockProp_blockBigCellMatrix (i : n) :
    IsUnit ((blockBigCellMatrix R b).toSquareBlockProp fun j => b j ≤ b i).det := by
  have h := IsLocalization.Away.isUnit_of_dvd
    (S := BlockBigCellCoordinateAlgebra R b) (blockBigCellDenominator R b)
    (Finset.dvd_prod_of_mem
      (fun k => ((Matrix.mvPolynomialX n n R).toSquareBlockProp fun j => b j ≤ b k).det)
      (Finset.mem_univ i))
  rw [blockBigCellMatrix, Matrix.map_toSquareBlockProp, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  exact h

/-- The block big cell is contained in the general linear group over any base ring. -/
theorem isUnit_det_blockBigCellMatrix : IsUnit (blockBigCellMatrix R b).det := by
  obtain ⟨L, D, U, hL, _, _, hU, hD, h⟩ :=
    (Matrix.exists_blockLDU_iff (blockBigCellMatrix R b)).mp
      isUnit_det_toSquareBlockProp_blockBigCellMatrix
  rw [h, Matrix.det_mul, Matrix.det_mul, hL.det_eq_one, hU.det_eq_one, one_mul, mul_one]
  exact hD

variable {S : Type*} [CommRing S] [Algebra R S]

/-- Evaluating the denominator gives the product of the leading block minors. -/
@[simp]
theorem aeval_blockBigCellDenominator (M : Matrix n n S) :
    MvPolynomial.aeval (Function.uncurry M) (blockBigCellDenominator R b) =
      ∏ i, (M.toSquareBlockProp fun j => b j ≤ b i).det := by
  simp only [blockBigCellDenominator, map_prod]
  exact Finset.prod_congr rfl fun i _ =>
    Matrix.aeval_det_submatrix_mvPolynomialX M Subtype.val Subtype.val

/-- Evaluation at a matrix whose leading block minors are units. -/
noncomputable def blockBigCellEval (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) :
    BlockBigCellCoordinateAlgebra R b →ₐ[R] S :=
  IsLocalization.Away.liftAlgHom (blockBigCellDenominator R b)
    (f := MvPolynomial.aeval (Function.uncurry M))
    (by simpa only [aeval_blockBigCellDenominator] using IsUnit.prod_univ_iff.mpr hM)

/-- Evaluation of a localized polynomial agrees with polynomial evaluation. -/
@[simp]
theorem blockBigCellEval_algebraMap (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det)
    (p : MvPolynomial (n × n) R) :
    blockBigCellEval (R := R) M hM (algebraMap _ _ p) =
      MvPolynomial.aeval (Function.uncurry M) p := by
  simp [blockBigCellEval]

/-- Evaluation recovers the matrix represented by the point. -/
@[simp]
theorem map_blockBigCellMatrix (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) :
    (blockBigCellMatrix R b).map (blockBigCellEval M hM) = M := by
  ext i j
  simp only [Matrix.map_apply, blockBigCellMatrix_apply, blockBigCellEval_algebraMap,
    MvPolynomial.aeval_X]
  exact Function.uncurry_apply_pair (f := M) i j

/-- Algebra maps out of the block big cell are determined by the universal matrix entries. -/
theorem blockBigCell_algHom_ext {f g : BlockBigCellCoordinateAlgebra R b →ₐ[R] S}
    (h : (blockBigCellMatrix R b).map f = (blockBigCellMatrix R b).map g) : f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (blockBigCellDenominator R b))
  apply MvPolynomial.algHom_ext
  intro ij
  simp only [AlgHom.comp_apply, Algebra.algHom, IsScalarTower.toAlgHom_apply]
  simpa only [Matrix.map_apply, blockBigCellMatrix_apply] using congrFun (congrFun h ij.1) ij.2

/-- Every algebra-valued point of the block big cell has invertible leading block minors. -/
theorem isUnit_det_toSquareBlockProp_map_blockBigCellMatrix
    (f : BlockBigCellCoordinateAlgebra R b →ₐ[R] S) (i : n) :
    IsUnit (((blockBigCellMatrix R b).map f).toSquareBlockProp fun j => b j ≤ b i).det :=
  (isUnit_det_toSquareBlockProp_blockBigCellMatrix i).det_map_toSquareBlockProp f.toRingHom

variable (R b S) in
/-- The block big cell represents matrices with invertible leading block minors, over every
commutative coefficient algebra. -/
noncomputable def blockBigCellPointsEquiv :
    (BlockBigCellCoordinateAlgebra R b →ₐ[R] S) ≃
      {M : Matrix n n S // ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det} where
  toFun f := ⟨(blockBigCellMatrix R b).map f,
    isUnit_det_toSquareBlockProp_map_blockBigCellMatrix f⟩
  invFun M := blockBigCellEval M.val M.property
  left_inv f := blockBigCell_algHom_ext
    (map_blockBigCellMatrix _ (isUnit_det_toSquareBlockProp_map_blockBigCellMatrix f))
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
theorem comp_blockBigCellEval {T : Type*} [CommRing T] [Algebra R T]
    (f : S →ₐ[R] T) (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det) :
    f.comp (blockBigCellEval M hM) = blockBigCellEval (M.map f)
      (fun i => (hM i).det_map_toSquareBlockProp f.toRingHom) := by
  apply blockBigCell_algHom_ext
  rw [AlgHom.coe_comp, ← Matrix.map_map, map_blockBigCellMatrix, map_blockBigCellMatrix]

variable (R b)

-- Choose the factors together so all three accessors share the same factorization.
private noncomputable def blockBigCellFactors :
    {t : Matrix n n (BlockBigCellCoordinateAlgebra R b) ×
        Matrix n n (BlockBigCellCoordinateAlgebra R b) ×
        Matrix n n (BlockBigCellCoordinateAlgebra R b) //
      t.1.BlockUnitriangular (toDual ∘ b) ∧ t.2.1.BlockTriangular b ∧
      t.2.1.BlockTriangular (toDual ∘ b) ∧ t.2.2.BlockUnitriangular b ∧
      IsUnit t.2.1.det ∧ blockBigCellMatrix R b = t.1 * t.2.1 * t.2.2} := by
  let h := (Matrix.exists_blockLDU_iff (blockBigCellMatrix R b)).mp
    isUnit_det_toSquareBlockProp_blockBigCellMatrix
  exact ⟨(h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose),
    h.choose_spec.choose_spec.choose_spec⟩

/-- The regular block lower unitriangular factor of the universal matrix. -/
noncomputable def blockBigCellLower : Matrix n n (BlockBigCellCoordinateAlgebra R b) :=
  (blockBigCellFactors R b).val.1

/-- The regular invertible block diagonal factor of the universal matrix. -/
noncomputable def blockBigCellDiag : Matrix n n (BlockBigCellCoordinateAlgebra R b) :=
  (blockBigCellFactors R b).val.2.1

/-- The regular block upper unitriangular factor of the universal matrix. -/
noncomputable def blockBigCellUpper : Matrix n n (BlockBigCellCoordinateAlgebra R b) :=
  (blockBigCellFactors R b).val.2.2

/-- The lower factor is block lower unitriangular. -/
theorem blockUnitriangular_blockBigCellLower :
    (blockBigCellLower R b).BlockUnitriangular (toDual ∘ b) :=
  (blockBigCellFactors R b).property.1

/-- The diagonal factor is block upper triangular. -/
theorem blockTriangular_blockBigCellDiag : (blockBigCellDiag R b).BlockTriangular b :=
  (blockBigCellFactors R b).property.2.1

/-- The diagonal factor is also block lower triangular. -/
theorem blockTriangular_blockBigCellDiag_toDual :
    (blockBigCellDiag R b).BlockTriangular (toDual ∘ b) :=
  (blockBigCellFactors R b).property.2.2.1

/-- The upper factor is block upper unitriangular. -/
theorem blockUnitriangular_blockBigCellUpper : (blockBigCellUpper R b).BlockUnitriangular b :=
  (blockBigCellFactors R b).property.2.2.2.1

/-- The diagonal factor is invertible in the coordinate algebra itself. -/
theorem isUnit_det_blockBigCellDiag : IsUnit (blockBigCellDiag R b).det :=
  (blockBigCellFactors R b).property.2.2.2.2.1

/-- The universal matrix is the product of its three regular block factors. -/
theorem blockBigCellMatrix_eq_blockBigCellLower_mul_blockBigCellDiag_mul_blockBigCellUpper :
    blockBigCellMatrix R b = blockBigCellLower R b * blockBigCellDiag R b * blockBigCellUpper R b :=
  (blockBigCellFactors R b).property.2.2.2.2.2

variable {R b}

private theorem map_blockBigCell_factors (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det)
    {L D U : Matrix n n S} (hL : L.BlockUnitriangular (toDual ∘ b))
    (hD : D.BlockTriangular b) (hD₁ : D.BlockTriangular (toDual ∘ b))
    (hU : U.BlockUnitriangular b) (h : M = L * D * U) :
    (blockBigCellLower R b).map (blockBigCellEval M hM) = L ∧
    (blockBigCellDiag R b).map (blockBigCellEval M hM) = D ∧
    (blockBigCellUpper R b).map (blockBigCellEval M hM) = U := by
  let f := blockBigCellEval (R := R) M hM
  apply Matrix.eq_of_blockLDU_eq ((blockUnitriangular_blockBigCellLower R b).map f)
    ((blockTriangular_blockBigCellDiag R b).map f)
    ((blockTriangular_blockBigCellDiag_toDual R b).map f)
    ((blockUnitriangular_blockBigCellUpper R b).map f) hL hD hD₁ hU
  · simpa only [← AlgHom.mapMatrix_apply, ← AlgHom.map_det]
      using (isUnit_det_blockBigCellDiag R b).map f
  · rw [← Matrix.map_mul, ← Matrix.map_mul,
      ← blockBigCellMatrix_eq_blockBigCellLower_mul_blockBigCellDiag_mul_blockBigCellUpper,
      map_blockBigCellMatrix, h]

/-- Evaluating the regular lower factor gives the lower factor of any block `LDU`
factorization of the represented point. -/
theorem map_blockBigCellLower (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det)
    {L D U : Matrix n n S} (hL : L.BlockUnitriangular (toDual ∘ b))
    (hD : D.BlockTriangular b) (hD₁ : D.BlockTriangular (toDual ∘ b))
    (hU : U.BlockUnitriangular b) (h : M = L * D * U) :
    (blockBigCellLower R b).map (blockBigCellEval M hM) = L :=
  (map_blockBigCell_factors M hM hL hD hD₁ hU h).1

/-- Evaluating the regular diagonal factor gives the diagonal factor of any block `LDU`
factorization of the represented point. -/
theorem map_blockBigCellDiag (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det)
    {L D U : Matrix n n S} (hL : L.BlockUnitriangular (toDual ∘ b))
    (hD : D.BlockTriangular b) (hD₁ : D.BlockTriangular (toDual ∘ b))
    (hU : U.BlockUnitriangular b) (h : M = L * D * U) :
    (blockBigCellDiag R b).map (blockBigCellEval M hM) = D :=
  (map_blockBigCell_factors M hM hL hD hD₁ hU h).2.1

/-- Evaluating the regular upper factor gives the upper factor of any block `LDU`
factorization of the represented point. -/
theorem map_blockBigCellUpper (M : Matrix n n S)
    (hM : ∀ i, IsUnit (M.toSquareBlockProp fun j => b j ≤ b i).det)
    {L D U : Matrix n n S} (hL : L.BlockUnitriangular (toDual ∘ b))
    (hD : D.BlockTriangular b) (hD₁ : D.BlockTriangular (toDual ∘ b))
    (hU : U.BlockUnitriangular b) (h : M = L * D * U) :
    (blockBigCellUpper R b).map (blockBigCellEval M hM) = U :=
  (map_blockBigCell_factors M hM hL hD hD₁ hU h).2.2

end TauCeti.GeneralLinear
