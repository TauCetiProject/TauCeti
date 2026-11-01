/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.HopfAlgebra

/-!
# Closed subschemes of the matrix affine space restricted to `GLₙ`

For a commutative ring `R`, the coordinate ring `O(GLₙ)` is the localization of the coordinate
ring `O(Mₙ) = R[Xᵢⱼ]` of the matrix affine space at the generic determinant. Let `J` be an ideal
of `O(Mₙ)`, cutting out a closed subscheme `Z` of `Mₙ`. The extension of `J` to `O(GLₙ)` cuts
out the closed subscheme `Z ∩ GLₙ` of `GLₙ`, and its coordinate ring is the localization of
`O(Mₙ) ⧸ J` at the class of the determinant: `Z ∩ GLₙ` is the open locus `det ≠ 0` in `Z`.

## Main declarations

* `TauCeti.GeneralLinear.quotientMapAlgEquivAway`: the equivalence
  `O(GLₙ) ⧸ J·O(GLₙ) ≃ₐ[R] (O(Mₙ) ⧸ J)[det⁻¹]`.
-/

public section

namespace TauCeti.GeneralLinear

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The coordinate ring `O(Mₙ) ⧸ J`, localized at the class of the generic determinant. -/
private abbrev QuotientAway (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n))) :=
  Localization.Away (Ideal.Quotient.mk J (Matrix.mvPolynomialX (Fin n) (Fin n) R).det)

private theorem isUnit_det_quotientAway (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n))) :
    IsUnit (((IsScalarTower.toAlgHom R _ (QuotientAway J)).comp (Ideal.Quotient.mkₐ R J))
      (Matrix.mvPolynomialX (Fin n) (Fin n) R).det) := by
  rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The map `O(GLₙ) → (O(Mₙ) ⧸ J)[det⁻¹]` induced by the quotient map. -/
private noncomputable def toQuotientAway (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n))) :
    coordinateHopfAlgebra R n →ₐ[R] QuotientAway J :=
  (IsLocalization.Away.liftAlgHom (S := CoordinateRing R n)
      (Matrix.mvPolynomialX (Fin n) (Fin n) R).det
      (f := (IsScalarTower.toAlgHom R _ (QuotientAway J)).comp (Ideal.Quotient.mkₐ R J))
      (isUnit_det_quotientAway J)).comp
    (coordinateHopfAlgebraAlgEquiv R n).symm.toAlgHom

private theorem toQuotientAway_coordinateRingMap
    (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n)))
    (p : MatrixMonoid.CoordinateRing R (Fin n)) :
    toQuotientAway J (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) =
      algebraMap _ (QuotientAway J) (Ideal.Quotient.mk J p) := by
  rw [toQuotientAway, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    coordinateRingMap_apply, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq,
    AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', Ideal.Quotient.mkₐ_eq_mk]

/-- The map `O(Mₙ) ⧸ J → O(GLₙ) ⧸ J·O(GLₙ)` induced by `O(Mₙ) → O(GLₙ)`. -/
private noncomputable def ofQuotient (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n))) :
    (MatrixMonoid.CoordinateRing R (Fin n) ⧸ J) →ₐ[R]
      coordinateHopfAlgebra R n ⧸
        J.map ((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n)) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp
    ((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n))) fun p hp ↦ by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hp

private theorem ofQuotient_mk (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n)))
    (p : MatrixMonoid.CoordinateRing R (Fin n)) :
    ofQuotient J (Ideal.Quotient.mk J p) =
      Ideal.Quotient.mk _ (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) := by
  rw [← Ideal.Quotient.mkₐ_eq_mk R J, ← AlgHom.comp_apply (ofQuotient J), ofQuotient,
    Ideal.Quotient.liftₐ_comp, AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    AlgEquiv.coe_toAlgHom]

/-- The map `(O(Mₙ) ⧸ J)[det⁻¹] → O(GLₙ) ⧸ J·O(GLₙ)`, extending `ofQuotient` across the
localization, since the determinant is a unit in `O(GLₙ)`. -/
private noncomputable def ofQuotientAway (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n))) :
    QuotientAway J →ₐ[R] coordinateHopfAlgebra R n ⧸
      J.map ((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n)) :=
  IsLocalization.Away.liftAlgHom
    (Ideal.Quotient.mk J (Matrix.mvPolynomialX (Fin n) (Fin n) R).det) (f := ofQuotient J) <| by
    rw [ofQuotient_mk, coordinateRingMap_apply]
    exact ((IsLocalization.Away.algebraMap_isUnit (S := CoordinateRing R n)
      (Matrix.mvPolynomialX (Fin n) (Fin n) R).det).map
      (coordinateHopfAlgebraAlgEquiv R n)).map (Ideal.Quotient.mk _)

private theorem ofQuotientAway_algebraMap_mk (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n)))
    (p : MatrixMonoid.CoordinateRing R (Fin n)) :
    ofQuotientAway J (algebraMap _ (QuotientAway J) (Ideal.Quotient.mk J p)) =
      Ideal.Quotient.mk _ (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) := by
  rw [ofQuotientAway, IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  exact ofQuotient_mk J p

/-- The map `O(GLₙ) ⧸ J·O(GLₙ) → (O(Mₙ) ⧸ J)[det⁻¹]` induced by `toQuotientAway`. -/
private noncomputable def quotientToQuotientAway
    (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n))) :
    coordinateHopfAlgebra R n ⧸
        J.map ((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n))
      →ₐ[R] QuotientAway J :=
  Ideal.Quotient.liftₐ _ (toQuotientAway J) fun a ha ↦ by
    refine RingHom.mem_ker.1 <|
      (Ideal.map_le_iff_le_comap (K := RingHom.ker (toQuotientAway J))).2
        (fun p hp ↦ ?_) ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom,
      toQuotientAway_coordinateRingMap, Ideal.Quotient.eq_zero_iff_mem.2 hp, map_zero]

private theorem quotientToQuotientAway_mk_coordinateRingMap
    (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n)))
    (p : MatrixMonoid.CoordinateRing R (Fin n)) :
    quotientToQuotientAway J
        (Ideal.Quotient.mk _ (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p))) =
      algebraMap _ (QuotientAway J) (Ideal.Quotient.mk J p) :=
  toQuotientAway_coordinateRingMap J p

/-- **A closed subscheme of `Mₙ` restricted to `GLₙ` is its determinant locus.** For an ideal `J`
of the coordinate ring `O(Mₙ)` of the matrix affine space, the quotient of `O(GLₙ)` by the
extension of `J` is the localization of `O(Mₙ) ⧸ J` at the class of the generic determinant. -/
noncomputable def quotientMapAlgEquivAway (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n))) :
    (coordinateHopfAlgebra R n ⧸
        J.map ((coordinateHopfAlgebraAlgEquiv R n).toAlgHom.comp (coordinateRingMap R n))) ≃ₐ[R]
      Localization.Away (Ideal.Quotient.mk J (Matrix.mvPolynomialX (Fin n) (Fin n) R).det) :=
  AlgEquiv.ofAlgHom (quotientToQuotientAway J) (ofQuotientAway J)
    (IsLocalization.algHom_ext (Submonoid.powers
        (Ideal.Quotient.mk J (Matrix.mvPolynomialX (Fin n) (Fin n) R).det)) <|
      Ideal.Quotient.algHom_ext _ <| MvPolynomial.algHom_ext fun ij ↦ by
        simp only [AlgHom.comp_apply, Algebra.algHom, IsScalarTower.coe_toAlgHom',
          Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq]
        rw [ofQuotientAway_algebraMap_mk, quotientToQuotientAway_mk_coordinateRingMap])
    (Ideal.Quotient.algHom_ext _ <| coordinateHopfAlgebra_algHom_ext R n fun i j ↦ by
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgHom.coe_id, id_eq]
      rw [quotientToQuotientAway_mk_coordinateRingMap, ofQuotientAway_algebraMap_mk])

/-- The equivalence sends the class of a polynomial coordinate function on `Mₙ`, read in
`O(GLₙ)`, to the class of the same function. -/
@[simp]
theorem quotientMapAlgEquivAway_mk_coordinateRingMap
    (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n)))
    (p : MatrixMonoid.CoordinateRing R (Fin n)) :
    quotientMapAlgEquivAway J
        (Ideal.Quotient.mk _ (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p))) =
      algebraMap _ _ (Ideal.Quotient.mk J p) := by
  rw [quotientMapAlgEquivAway, ← AlgEquiv.coe_toAlgHom, AlgEquiv.toAlgHom_ofAlgHom,
    quotientToQuotientAway_mk_coordinateRingMap]

/-- The inverse equivalence sends the class of a polynomial coordinate function on `Mₙ` to the
class of the same function in `O(GLₙ)`. -/
@[simp]
theorem quotientMapAlgEquivAway_symm_algebraMap_mk
    (J : Ideal (MatrixMonoid.CoordinateRing R (Fin n)))
    (p : MatrixMonoid.CoordinateRing R (Fin n)) :
    (quotientMapAlgEquivAway J).symm (algebraMap _ _ (Ideal.Quotient.mk J p)) =
      Ideal.Quotient.mk _ (coordinateHopfAlgebraAlgEquiv R n (coordinateRingMap R n p)) := by
  rw [AlgEquiv.symm_apply_eq, quotientMapAlgEquivAway_mk_coordinateRingMap]

end TauCeti.GeneralLinear
