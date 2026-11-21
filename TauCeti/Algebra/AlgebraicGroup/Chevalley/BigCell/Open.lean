/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Coordinate
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BigCell.Basic
public import TauCeti.LinearAlgebra.Matrix.LDU.Coordinates
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
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BigCell.Basic`. The denominator uses the
leading-minor product from `TauCeti.LinearAlgebra.Matrix.LDU.Coordinates`.

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
  Matrix.leadingBlockMinorProduct (fun j => r ⟨D.weight j, Set.mem_range_self j⟩) D.coordinateMatrix

/-- The denominator is the leading-block-minor product for the induced ranking of the basis. -/
theorem blockBigCellDenominator_def :
    D.blockBigCellDenominator r =
      Matrix.leadingBlockMinorProduct (fun j => r ⟨D.weight j, Set.mem_range_self j⟩)
        D.coordinateMatrix :=
  (rfl)

/-- The coordinate algebra of the intersection with the weight-block LDU locus. -/
abbrev BlockBigCellCoordinateAlgebra := Localization.Away (D.blockBigCellDenominator r)

/-- The integral weight-block open subscheme of the Chevalley group. -/
abbrev blockBigCell : Scheme := Spec (CommRingCat.of (D.BlockBigCellCoordinateAlgebra r))

/-- The inclusion of the weight-block open into the actual Chevalley group scheme. -/
def blockBigCellι : D.blockBigCell r ⟶ D.groupScheme.X.left :=
  Spec.map (CommRingCat.ofHom (algebraMap D.coordinateHopfAlgebra
    (D.BlockBigCellCoordinateAlgebra r))) ≫ eqToHom D.groupScheme_X_left.symm

/-- The inclusion is induced by localization of the Chevalley coordinate algebra. -/
theorem blockBigCellι_def :
    D.blockBigCellι r = Spec.map (CommRingCat.ofHom (algebraMap D.coordinateHopfAlgebra
      (D.BlockBigCellCoordinateAlgebra r))) ≫ eqToHom D.groupScheme_X_left.symm :=
  (rfl)

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
  simp [blockBigCellι_def]

/-- The inclusion into the Chevalley group scheme respects the structure map to `Spec ℤ`. -/
@[reassoc (attr := simp↓)]
theorem blockBigCellι_comp_groupScheme_X_hom :
    D.blockBigCellι r ≫ D.groupScheme.X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (D.BlockBigCellCoordinateAlgebra r))) := by
  have h : D.groupScheme.X.hom = eqToHom D.groupScheme_X_left ≫
      Spec.map (CommRingCat.ofHom (algebraMap ℤ D.coordinateHopfAlgebra)) :=
    hopfSpec_obj_X_hom ℤ D.coordinateHopfAlgebra
  rw [h, ← Category.assoc, blockBigCellι_comp_eqToHom, ← Spec.map_comp,
    IsScalarTower.algebraMap_eq ℤ D.coordinateHopfAlgebra (D.BlockBigCellCoordinateAlgebra r)]
  rfl

/-- The universal matrix on the weight-block open. -/
def blockBigCellMatrix :
    Matrix (Fin D.dim) (Fin D.dim) (D.BlockBigCellCoordinateAlgebra r) :=
  D.coordinateMatrix.map (algebraMap _ _)

/-- The universal matrix on the open is the localization of the Chevalley coordinate matrix. -/
theorem blockBigCellMatrix_def :
    D.blockBigCellMatrix r = D.coordinateMatrix.map
      (algebraMap D.coordinateHopfAlgebra (D.BlockBigCellCoordinateAlgebra r)) :=
  (rfl)

/-- The entries of the matrix on the open are the localized Chevalley matrix entries. -/
@[simp]
theorem blockBigCellMatrix_apply (i j : Fin D.dim) :
    D.blockBigCellMatrix r i j = algebraMap D.coordinateHopfAlgebra
      (D.BlockBigCellCoordinateAlgebra r) (D.coordinateMatrix i j) :=
  (rfl)

section Denominator

variable {A F : Type*} [CommRing A] [FunLike F D.coordinateHopfAlgebra A]
  [RingHomClass F D.coordinateHopfAlgebra A]

/-- Evaluation sends the denominator to the product of leading weight-block minors. -/
@[simp]
theorem map_blockBigCellDenominator (f : F) :
    f (D.blockBigCellDenominator r) = ∏ i, ((D.coordinateMatrix.map f).toSquareBlockProp
      fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
        r ⟨D.weight i, Set.mem_range_self i⟩).det := by
  have h := Matrix.leadingBlockMinorProduct_map (fun j => r ⟨D.weight j, Set.mem_range_self j⟩)
    D.coordinateMatrix (RingHomClass.toRingHom f)
  rw [RingHom.coe_coe] at h
  rw [blockBigCellDenominator_def, ← h, Matrix.leadingBlockMinorProduct_def]

/-- The image of the denominator is a unit exactly when all leading weight-block minors of the
image matrix are units. -/
theorem isUnit_map_blockBigCellDenominator_iff (f : F) :
    IsUnit (f (D.blockBigCellDenominator r)) ↔ ∀ i,
      IsUnit ((D.coordinateMatrix.map f).toSquareBlockProp
        fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
          r ⟨D.weight i, Set.mem_range_self i⟩).det := by
  rw [D.map_blockBigCellDenominator r, IsUnit.prod_univ_iff]

end Denominator

/-- Each leading weight-block minor of the universal matrix is a unit. -/
theorem isUnit_det_toSquareBlockProp_blockBigCellMatrix (i : Fin D.dim) :
    IsUnit ((D.blockBigCellMatrix r).toSquareBlockProp
      fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
        r ⟨D.weight i, Set.mem_range_self i⟩).det := by
  rw [blockBigCellMatrix_def]
  exact (D.isUnit_map_blockBigCellDenominator_iff r (algebraMap _ _)).mp
    (IsLocalization.Away.algebraMap_isUnit _) i

/-- The localization lift evaluates the matrix on the open by evaluating the original entries. -/
@[simp↓]
theorem map_blockBigCellMatrix_liftAlgHom {S : Type*} [CommSemiring S] [Algebra ℤ S]
    (f : D.coordinateHopfAlgebra →ₐ[ℤ] S) (hf : IsUnit (f (D.blockBigCellDenominator r))) :
    (D.blockBigCellMatrix r).map
      (IsLocalization.Away.liftAlgHom (D.blockBigCellDenominator r) hf :
        D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] S) = D.coordinateMatrix.map f := by
  ext i j
  simp only [Matrix.map_apply, blockBigCellMatrix_apply, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

variable {A : Type*} [CommRing A] [Algebra ℤ A]

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
  invFun g := IsLocalization.Away.liftAlgHom (D.blockBigCellDenominator r)
    (f := (((D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)).symm g.val).ofConv)
    ((D.isUnit_map_blockBigCellDenominator_iff r _).mpr (by
      simpa only [D.map_coordinateMatrix, toConv_ofConv, MulEquiv.apply_symm_apply]
        using g.property))
  left_inv f := by
    apply Localization.algHom_ext (Submonoid.powers (D.blockBigCellDenominator r))
    ext x
    simp only [MulEquiv.symm_apply_apply, ofConv_toConv, AlgHom.comp_apply, Algebra.algHom,
      IsScalarTower.toAlgHom_apply, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
  right_inv g := by
    apply Subtype.ext
    apply ((D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)).symm.injective
    apply WithConv.ext
    apply AlgHom.ext
    intro x
    simp only [MulEquiv.symm_apply_apply, ofConv_toConv, AlgHom.comp_apply,
      IsScalarTower.toAlgHom_apply, IsLocalization.Away.coe_liftAlgHom, IsLocalization.Away.lift_eq,
      AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

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
      (((D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)).symm g.val).ofConv x := by
  simp only [blockBigCellPointsEquiv, Equiv.coe_fn_symm_mk, IsLocalization.Away.coe_liftAlgHom,
    IsLocalization.Away.lift_eq, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]

/-- The inverse point comparison restricts to the original Chevalley coordinate map. -/
@[simp]
theorem blockBigCellPointsEquiv_symm_comp_toAlgHom
    (g : {g : D.points A // ∀ i,
      IsUnit ((g.val : Matrix (Fin D.dim) (Fin D.dim) A).toSquareBlockProp
        fun j => r ⟨D.weight j, Set.mem_range_self j⟩ ≤
          r ⟨D.weight i, Set.mem_range_self i⟩).det}) :
    ((D.blockBigCellPointsEquiv r).symm g).comp
        (IsScalarTower.toAlgHom ℤ D.coordinateHopfAlgebra (D.BlockBigCellCoordinateAlgebra r)) =
      (((D.pointsPresentation A).mulEquiv (A := CommAlgCat.of ℤ A)).symm g.val).ofConv := by
  ext x
  exact D.blockBigCellPointsEquiv_symm_algebraMap r g x

/-- Evaluation of the matrix on the open is the underlying matrix of its Chevalley point. -/
theorem map_blockBigCellMatrix (f : D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] A) :
    (D.blockBigCellMatrix r).map f =
      (((D.blockBigCellPointsEquiv r f).val).val : Matrix (Fin D.dim) (Fin D.dim) A) := by
  rw [blockBigCellPointsEquiv_apply, ← D.map_coordinateMatrix]
  simp only [blockBigCellMatrix_def, Matrix.map_map, AlgHom.coe_comp,
    IsScalarTower.coe_toAlgHom']

/-- The point comparison commutes with arbitrary homomorphisms of value rings. -/
theorem blockBigCellPointsEquiv_comp {B : Type*} [CommRing B] [Algebra ℤ B] (φ : A →ₐ[ℤ] B)
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
    (D.isUnit_det_toSquareBlockProp_blockBigCellMatrix r)

/-- The ambient comparison is evaluation at the universal matrix of the Chevalley open. -/
theorem blockBigCellAmbientCoordinateMap_def :
    D.blockBigCellAmbientCoordinateMap r = GeneralLinear.blockBigCellEval (D.blockBigCellMatrix r)
      (D.isUnit_det_toSquareBlockProp_blockBigCellMatrix r) :=
  (rfl)

/-- The ambient-coordinate comparison preserves the universal matrix, so every regular LDU
coordinate can be evaluated on the Chevalley open without a choice of factorization. -/
@[simp]
theorem map_blockBigCellMatrix_blockBigCellAmbientCoordinateMap :
    (GeneralLinear.blockBigCellMatrix ℤ (fun j => r ⟨D.weight j, Set.mem_range_self j⟩)).map
        (D.blockBigCellAmbientCoordinateMap r) = D.blockBigCellMatrix r :=
  GeneralLinear.map_blockBigCellMatrix _ _

/-- Specializing the ambient coordinate map is evaluation at the specialized Chevalley matrix. -/
theorem comp_blockBigCellAmbientCoordinateMap (f : D.BlockBigCellCoordinateAlgebra r →ₐ[ℤ] A) :
    f.comp (D.blockBigCellAmbientCoordinateMap r) =
      GeneralLinear.blockBigCellEval ((D.blockBigCellMatrix r).map f)
        (fun i => (D.isUnit_det_toSquareBlockProp_blockBigCellMatrix r i).det_map_toSquareBlockProp
          f.toRingHom) := by
  rw [blockBigCellAmbientCoordinateMap_def, GeneralLinear.comp_blockBigCellEval]

end

end TauCeti.DynkinType.ChevalleyDatum
