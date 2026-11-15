/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BigCell.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The integral weight-block open of a Chevalley datum

For an ordering `r` of the distinct weights, invert the product of the leading weight-block
minors in the datum's actual integral coordinate algebra. The resulting affine scheme is an
open subscheme of the Chevalley group. Over every commutative value ring, its points are exactly
the Chevalley points whose leading weight-block minors are units. Thus it realizes the
intersection with the matrix block-LDU locus, including on nonreduced algebras, not just on
field-valued points.

The open carries a canonical map from the ambient block-big-cell coordinate algebra. This
restricts the regular matrix LDU coordinates to the Chevalley open. It does not assert that
these matrix factors lie in the negative-root-generated subgroup, the weight torus, and the
positive-root-generated subgroup: that is an additional group-theoretic assertion. The construction
permits any ordering of distinct weights; for the usual big cell one orders them compatibly with
dominance.

The matrix open and its localization API are those of
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BigCell.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory WithConv

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable {β : Type*} [LinearOrder β] (r : Set.range D.weight ≃ β)

/-- The product of the leading weight-block minors in the actual coordinate algebra.
Repeated weights repeat factors, without changing the principal open. -/
def blockBigCellDenominator : D.coordinateHopfAlgebra :=
  ∏ i, (D.coordinateMatrix.toSquareBlockProp
    fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤ r ⟨D.weight i, Set.mem_range_self i⟩).det

/-- The defining product of the actual coordinate matrix's leading weight-block minors. -/
theorem blockBigCellDenominator_def :
    D.blockBigCellDenominator r = ∏ i, (D.coordinateMatrix.toSquareBlockProp
      fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
        r ⟨D.weight i, Set.mem_range_self i⟩).det :=
  (rfl)

/-- The coordinate algebra of the intersection with the weight-block LDU locus. -/
abbrev BlockBigCellCoordinateAlgebra := Localization.Away (D.blockBigCellDenominator r)

/-- The integral weight-block open subscheme of the Chevalley group. -/
abbrev blockBigCell : Scheme := Spec (CommRingCat.of (D.BlockBigCellCoordinateAlgebra r))

/-- The inclusion of the weight-block open into the actual Chevalley group scheme. -/
def blockBigCellι : D.blockBigCell r ⟶ D.groupScheme.X.left :=
  Spec.map (CommRingCat.ofHom (algebraMap D.coordinateHopfAlgebra
    (D.BlockBigCellCoordinateAlgebra r))) ≫ eqToHom D.groupScheme_X_left.symm

/-- The weight-block locus is open over the integers, not merely in each geometric fibre. -/
instance isOpenImmersion_blockBigCellι : IsOpenImmersion (D.blockBigCellι r) := by
  have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap D.coordinateHopfAlgebra
      (Localization.Away (D.blockBigCellDenominator r))))) := inferInstance
  -- State the localization instance before composing with the named scheme presentation.
  exact @IsOpenImmersion.comp _ _ _ _ _ this inferInstance

/-- In coordinate spectra, the inclusion is the spectrum of the localization map. -/
@[reassoc (attr := simp)]
theorem blockBigCellι_comp_eqToHom :
    D.blockBigCellι r ≫ eqToHom D.groupScheme_X_left =
      Spec.map (CommRingCat.ofHom (algebraMap D.coordinateHopfAlgebra
        (D.BlockBigCellCoordinateAlgebra r))) := by
  simp [blockBigCellι]

/-- The universal matrix on the weight-block open. -/
def blockBigCellMatrix :
    Matrix (Fin D.dim) (Fin D.dim) (D.BlockBigCellCoordinateAlgebra r) :=
  D.coordinateMatrix.map (algebraMap _ _)

/-- Each leading weight-block minor of the universal matrix is a unit. -/
theorem isUnit_leading_minor_blockBigCellMatrix (i : Fin D.dim) :
    IsUnit ((D.blockBigCellMatrix r).toSquareBlockProp
      fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
        r ⟨D.weight i, Set.mem_range_self i⟩).det := by
  have h := IsLocalization.Away.isUnit_of_dvd
    (S := D.BlockBigCellCoordinateAlgebra r) (D.blockBigCellDenominator r)
    (Finset.dvd_prod_of_mem (fun k => (D.coordinateMatrix.toSquareBlockProp
      fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤ r ⟨D.weight k, Set.mem_range_self k⟩).det)
      (Finset.mem_univ i))
  rw [blockBigCellMatrix, Matrix.map_toSquareBlockProp, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det]
  exact h

variable {A : Type*} [CommRing A]

/-- Evaluating the denominator multiplies the leading weight-block minors of the point's matrix. -/
@[simp]
theorem map_blockBigCellDenominator (f : D.coordinateHopfAlgebra →ₐ[ℤ] A) :
    f (D.blockBigCellDenominator r) = ∏ i, ((D.coordinateMatrix.map f).toSquareBlockProp
      fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
        r ⟨D.weight i, Set.mem_range_self i⟩).det := by
  simp only [blockBigCellDenominator, map_prod]
  exact Finset.prod_congr rfl fun i _ => by
    rw [Matrix.map_toSquareBlockProp, ← AlgHom.mapMatrix_apply, ← AlgHom.map_det]

/-- A coordinate point extends to the weight-block open exactly when all its leading
weight-block minors are units. No reducedness or field hypothesis is required. -/
theorem isUnit_map_blockBigCellDenominator_iff (f : D.coordinateHopfAlgebra →ₐ[ℤ] A) :
    IsUnit (f (D.blockBigCellDenominator r)) ↔ ∀ i,
      IsUnit ((D.coordinateMatrix.map f).toSquareBlockProp
        fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
          r ⟨D.weight i, Set.mem_range_self i⟩).det := by
  rw [D.map_blockBigCellDenominator r, IsUnit.prod_univ_iff]

section Evaluation

variable {S : Type*} [CommSemiring S] [Algebra ℤ S]

/-- Extension of a Chevalley coordinate point to the weight-block open. -/
def blockBigCellEval (f : D.coordinateHopfAlgebra →ₐ[ℤ] S)
    (hf : IsUnit (f (D.blockBigCellDenominator r))) :
    D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] S :=
  IsLocalization.Away.liftAlgHom (D.blockBigCellDenominator r) hf

/-- The extension agrees with the original coordinate point. -/
@[simp]
theorem blockBigCellEval_algebraMap (f : D.coordinateHopfAlgebra →ₐ[ℤ] S)
    (hf : IsUnit (f (D.blockBigCellDenominator r))) (x : D.coordinateHopfAlgebra) :
    D.blockBigCellEval r f hf (algebraMap _ _ x) = f x := by
  simp [blockBigCellEval]

end Evaluation

/-- Maps out of the weight-block open are determined on the Chevalley coordinate algebra. -/
@[ext]
theorem blockBigCell_algHom_ext {S : Type*} [Semiring S] [Algebra ℤ S]
    {f g : D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] S}
    (h : ∀ x : D.coordinateHopfAlgebra, f (algebraMap _ _ x) = g (algebraMap _ _ x)) :
    f = g := by
  apply IsLocalization.algHom_ext (Submonoid.powers (D.blockBigCellDenominator r))
  exact AlgHom.ext h

/-- The algebra-valued points of the integral open are precisely the actual Chevalley
points with unit leading weight-block minors. -/
def blockBigCellPointsEquiv :
    (D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] A) ≃
      {g : D.points A // ∀ i,
        IsUnit ((g.val : Matrix (Fin D.dim) (Fin D.dim) A).toSquareBlockProp
          fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
            r ⟨D.weight i, Set.mem_range_self i⟩).det} where
  toFun f :=
    ⟨(D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)
        (toConv (f.comp (IsScalarTower.toAlgHom ℤ D.coordinateHopfAlgebra _))), by
      rw [← D.map_coordinateMatrix]
      apply (D.isUnit_map_blockBigCellDenominator_iff r _).mp
      exact (IsLocalization.Away.algebraMap_isUnit (D.blockBigCellDenominator r)).map f⟩
  invFun g := D.blockBigCellEval r
    (((D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)).symm g.val).ofConv
    ((D.isUnit_map_blockBigCellDenominator_iff r _).mpr (by
      simpa only [D.map_coordinateMatrix, toConv_ofConv, MulEquiv.apply_symm_apply]
        using g.property))
  left_inv f := by
    apply D.blockBigCell_algHom_ext r
    intro x
    simp only [MulEquiv.symm_apply_apply, ofConv_toConv]
    exact D.blockBigCellEval_algebraMap r _ _ x
  right_inv g := by
    apply Subtype.ext
    apply ((D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)).symm.injective
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    simp only [MulEquiv.symm_apply_apply, ofConv_toConv, AlgHom.comp_apply,
      IsScalarTower.toAlgHom_apply]
    exact D.blockBigCellEval_algebraMap r _ _ x

/-- The point of the Chevalley group underlying a point of the open is obtained by
restriction along the coordinate localization map. -/
@[simp]
theorem blockBigCellPointsEquiv_apply (f : D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] A) :
    (D.blockBigCellPointsEquiv r f).val =
      (D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)
        (toConv (f.comp (IsScalarTower.toAlgHom ℤ D.coordinateHopfAlgebra _))) :=
  (rfl)

/-- The inverse point comparison agrees with the given Chevalley point on its coordinate
algebra. This is the characteristic equation of the unique lift to the open. -/
@[simp]
theorem blockBigCellPointsEquiv_symm_algebraMap
    (g : {g : D.points A // ∀ i,
      IsUnit ((g.val : Matrix (Fin D.dim) (Fin D.dim) A).toSquareBlockProp
        fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤ r ⟨D.weight i, Set.mem_range_self i⟩).det})
    (x : D.coordinateHopfAlgebra) :
    (D.blockBigCellPointsEquiv r).symm g (algebraMap _ _ x) =
      (((D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)).symm g.val).ofConv x :=
  D.blockBigCellEval_algebraMap r _ _ x

/-- Evaluation of the matrix on the open is the underlying matrix of its Chevalley point. -/
@[simp]
theorem map_blockBigCellMatrix (f : D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] A) :
    (D.blockBigCellMatrix r).map f =
      (((D.blockBigCellPointsEquiv r f).val).val : Matrix (Fin D.dim) (Fin D.dim) A) := by
  rw [blockBigCellPointsEquiv_apply, ← D.map_coordinateMatrix]
  simp only [blockBigCellMatrix, Matrix.map_map, AlgHom.coe_comp,
    IsScalarTower.coe_toAlgHom']

/-- The point comparison commutes with arbitrary homomorphisms of value rings. -/
theorem blockBigCellPointsEquiv_comp {B : Type*} [CommRing B] (φ : A →ₐ[ℤ] B)
    (f : D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] A) :
    (D.blockBigCellPointsEquiv r (φ.comp f)).val =
      (D.pointsPresentation A).map (D.pointsPresentation B) φ.toRingHom
        (D.blockBigCellPointsEquiv r f).val := by
  apply Subtype.ext
  rw [GeneralLinear.IntegralPointsPresentation.coe_map]
  apply Units.ext
  simp only [Matrix.GeneralLinearGroup.val_map_apply, ← D.map_blockBigCellMatrix,
    Matrix.map_map, AlgHom.coe_comp]
  rfl

/-- The ambient regular block-LDU coordinates restrict to the Chevalley open. -/
def blockBigCellAmbientCoordinateMap :
    GeneralLinear.BlockBigCellCoordinateAlgebra ℤ
      (fun j => r ⟨D.weight j, Set.mem_range_self j⟩) →ₐ[ℤ] D.BlockBigCellCoordinateAlgebra r :=
  GeneralLinear.blockBigCellEval (D.blockBigCellMatrix r)
    (D.isUnit_leading_minor_blockBigCellMatrix r)

/-- The ambient-coordinate comparison preserves the universal matrix, so every regular LDU
coordinate can be evaluated on the Chevalley open without a choice of factorization. -/
@[simp]
theorem map_blockBigCellMatrix_ambient :
    (GeneralLinear.blockBigCellMatrix ℤ (fun j => r ⟨D.weight j, Set.mem_range_self j⟩)).map
        (D.blockBigCellAmbientCoordinateMap r) = D.blockBigCellMatrix r :=
  GeneralLinear.map_blockBigCellMatrix _ _

end

end TauCeti.DynkinType.ChevalleyDatum
