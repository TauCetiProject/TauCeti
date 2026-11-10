/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BigCell.Basic
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion

/-!
# The block big cell as an open subscheme of the general linear group

The regular block LDU coordinates give an open immersion into the actual general linear
scheme, not just into matrix space. Its coordinate map sends each generic entry to the
corresponding entry of the universal block-big-cell matrix. Over every coefficient algebra,
a point of the general linear scheme factors uniquely through this open exactly when its
leading block minors are units.

This realizes the ambient matrix open used to intersect a represented group scheme with the
block LDU locus. It does not assert that the LDU factors of such an intersection belong to
that group scheme. The coordinate algebra and regular factors are those of
`TauCeti.Algebra.AlgebraicGroup.GeneralLinear.BigCell.Basic`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 5, Theorem 7.
* J. C. Jantzen, *Representations of Algebraic Groups*, second edition, II.1.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.GeneralLinear

noncomputable section

universe u v

variable (R : Type u) [CommRing R] (n : ℕ)
variable {α : Type*} [LinearOrder α] (b : Fin n → α)

private theorem isUnit_det_coordinateMap :
    IsUnit ((IsScalarTower.toAlgHom R (MatrixMonoid.CoordinateRing R (Fin n))
      (BlockBigCellCoordinateAlgebra R b))
      (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))) := by
  have hmatrix :
      (Matrix.mvPolynomialX (Fin n) (Fin n) R).map
          (algebraMap _ (BlockBigCellCoordinateAlgebra R b)) = blockBigCellMatrix R b := by
    ext i j
    simp [Matrix.mvPolynomialX, blockBigCellMatrix_apply]
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, IsScalarTower.coe_toAlgHom', hmatrix]
  exact isUnit_det_blockBigCellMatrix

/-- The coordinate map of the block-big-cell inclusion into `GLₙ`, extending the polynomial
coordinate map across inversion of the determinant. -/
def blockBigCellCoordinateMap :
    CoordinateRing R n →ₐ[R] BlockBigCellCoordinateAlgebra R b :=
  IsLocalization.Away.liftAlgHom
    (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R))
    (isUnit_det_coordinateMap R n b)

/-- The inclusion preserves every polynomial in the matrix entries. -/
@[simp]
theorem blockBigCellCoordinateMap_coordinateRingMap (p : MvPolynomial (Fin n × Fin n) R) :
    blockBigCellCoordinateMap R n b (coordinateRingMap R n p) =
      algebraMap _ (BlockBigCellCoordinateAlgebra R b) p := by
  rw [coordinateRingMap_apply, blockBigCellCoordinateMap,
    IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  rfl

/-- The inclusion sends the localized generic matrix to the universal block-big-cell matrix. -/
@[simp]
theorem map_localizedGenericMatrix_blockBigCellCoordinateMap :
    (localizedGenericMatrix R n).map (blockBigCellCoordinateMap R n b) =
      blockBigCellMatrix R b := by
  ext i j
  simp [blockBigCellMatrix_apply]

/-- The block big cell, with its existing regular LDU coordinates, included in the underlying
scheme of the general linear group. -/
def blockBigCellι :
    Spec (CommRingCat.of (BlockBigCellCoordinateAlgebra R b)) ⟶ (groupScheme R n).X.left :=
  Spec.map (CommRingCat.ofHom (blockBigCellCoordinateMap R n b).toRingHom) ≫
    (groupSchemeSpecIso R n).inv

/-- In determinant-localization coordinates, the inclusion is the spectrum of its coordinate
map. -/
@[simp]
theorem blockBigCellι_comp_groupSchemeSpecIso :
    blockBigCellι R n b ≫ (groupSchemeSpecIso R n).hom =
      Spec.map (CommRingCat.ofHom (blockBigCellCoordinateMap R n b).toRingHom) := by
  simp [blockBigCellι]

private theorem blockBigCellCoordinateMap_comp :
    Spec.map (CommRingCat.ofHom (blockBigCellCoordinateMap R n b).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial (Fin n × Fin n) R) (CoordinateRing R n))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap (MvPolynomial (Fin n × Fin n) R)
          (BlockBigCellCoordinateAlgebra R b))) := by
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  simpa only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom,
    coordinateRingMap_apply, MatrixMonoid.CoordinateRing, AlgHom.toRingHom_eq_coe,
    AlgHom.coe_toRingHom] using
      blockBigCellCoordinateMap_coordinateRingMap R n b p

/-- The block-big-cell inclusion is an open immersion over every commutative base ring. -/
instance isOpenImmersion_blockBigCellι : IsOpenImmersion (blockBigCellι R n b) := by
  have hcomp := blockBigCellCoordinateMap_comp R n b
  have : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (blockBigCellCoordinateMap R n b).toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (MvPolynomial (Fin n × Fin n) R) (CoordinateRing R n)))) := by
    rw [hcomp]
    infer_instance
  have := IsOpenImmersion.of_comp
    (Spec.map (CommRingCat.ofHom (blockBigCellCoordinateMap R n b).toRingHom))
    (Spec.map (CommRingCat.ofHom
      (algebraMap (MvPolynomial (Fin n × Fin n) R) (CoordinateRing R n))))
  unfold blockBigCellι
  infer_instance

/-- The inclusion commutes with the structural morphisms to the base. -/
@[reassoc]
theorem blockBigCellι_comp_structure :
    blockBigCellι R n b ≫ (groupScheme R n).X.hom =
      Spec.map (CommRingCat.ofHom (algebraMap R (BlockBigCellCoordinateAlgebra R b))) := by
  rw [groupScheme_X_hom, ← Category.assoc, blockBigCellι_comp_groupSchemeSpecIso,
    ← Spec.map_comp]
  congr 1
  ext r
  exact (blockBigCellCoordinateMap R n b).commutes r

variable {S : Type v} [CommRing S] [Algebra R S]

/-- An algebra-valued point of `GLₙ` factors uniquely through the block big cell if and only
if every leading block minor of its matrix is a unit. This includes nonreduced value rings. -/
theorem existsUnique_comp_blockBigCellCoordinateMap_iff (f : CoordinateRing R n →ₐ[R] S) :
    (∃! g : BlockBigCellCoordinateAlgebra R b →ₐ[R] S,
      g.comp (blockBigCellCoordinateMap R n b) = f) ↔
      ∀ i, IsUnit ((((localizedGenericMatrix R n).map f).toSquareBlockProp
        fun j => b j ≤ b i).det) := by
  constructor
  · rintro ⟨g, rfl, _⟩
    rw [AlgHom.coe_comp, ← Matrix.map_map, map_localizedGenericMatrix_blockBigCellCoordinateMap]
    exact isUnit_det_toSquareBlockProp_map_blockBigCellMatrix g
  · intro hf
    let M := (localizedGenericMatrix R n).map f
    let g := blockBigCellEval (R := R) M hf
    have hg : g.comp (blockBigCellCoordinateMap R n b) = f := by
      apply IsLocalization.algHom_ext
        (Submonoid.powers (Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) R)))
      apply MvPolynomial.algHom_ext
      rintro ⟨i, j⟩
      simp [Algebra.algHom, g, M, Function.uncurry]
    refine ⟨g, hg, fun g' hg' => ?_⟩
    apply blockBigCell_algHom_ext
    have h := congrArg (fun q : CoordinateRing R n →ₐ[R] S =>
      (localizedGenericMatrix R n).map q) (hg'.trans hg.symm)
    simpa only [AlgHom.coe_comp, ← Matrix.map_map,
      map_localizedGenericMatrix_blockBigCellCoordinateMap] using h

end

end TauCeti.GeneralLinear
