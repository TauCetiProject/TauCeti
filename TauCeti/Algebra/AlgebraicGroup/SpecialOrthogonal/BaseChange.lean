/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.SpecialOrthogonal.Basic

/-!
# Base change of the special orthogonal group

For a morphism of commutative rings `R → K`, scalar extension of the coordinate Hopf algebra
of the standard special orthogonal group `SOₙ` is canonically the coordinate Hopf algebra
constructed directly over `K`.

These isomorphisms specialize the scalar-extension comparisons of
`TauCeti.ConstantForm.Special` to the identity form.

## Main declarations

* `TauCeti.SpecialOrthogonal.coordinateHopfAlgebraBaseChangeIso`: base change of the coordinate
  Hopf algebra of `SOₙ`.
* `baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom`: compatibility with
  the quotient coordinate morphisms from `O(GLₙ)`.
* `TauCeti.SpecialOrthogonal.finiteTypeCoordinateHopfAlgebraBaseChangeIso`: the finite-type form
  of the same isomorphism.
* `TauCeti.SpecialOrthogonal.groupSchemeBaseChangeIso`: base change of the group scheme `SOₙ`,
  compatible with the inclusions into `GLₙ`
  (`map_inclusion_comp_groupSchemeBaseChangeIso_hom`).

## References

* J. S. Milne, *Basic Theory of Affine Group Schemes*, Chapter IV, §1.8.
* The Stacks Project, Tags [01JO](https://stacks.math.columbia.edu/tag/01JO) and
  [022W](https://stacks.math.columbia.edu/tag/022W).

The scalar-extension compatibility is used for geometric connectedness and reductivity of `SOₙ`.
-/

public section

open CategoryTheory Matrix
namespace TauCeti.SpecialOrthogonal

universe u v

section Coordinate

variable (R : Type u) (K : Type max u v) [CommRing R] [CommRing K] [Algebra R K]
variable (n : ℕ)

/-- Base change of the special-orthogonal coordinate Hopf algebra is canonically the
special-orthogonal coordinate Hopf algebra over the new base. -/
noncomputable def coordinateHopfAlgebraBaseChangeIso :
    CommHopfAlgCat.baseChange (K := K) (coordinateHopfAlgebra R n) ≅
      coordinateHopfAlgebra K n :=
  eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
      (coordinateHopfAlgebra_eq_special R n)) ≪≫
    ConstantForm.Special.coordinateHopfAlgebraBaseChangeIso
      (Matrix.map_one (n := Fin n) (algebraMap R K) (map_zero _) (map_one _)) ≪≫
    eqToIso (coordinateHopfAlgebra_eq_special K n).symm

/-- The special-orthogonal base-change isomorphism is compatible with the quotient coordinate
morphisms from the corresponding general-linear coordinate Hopf algebras. -/
@[simp]
theorem baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom :
    CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n) ≫
        (coordinateHopfAlgebraBaseChangeIso R K n).hom =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).hom ≫ coordinateMap K n := by
  have hR := CommHopfAlgCat.mkQuotient_comp_eqToHom (definingHopfIdeal_eq_special R n).symm
  have hK := CommHopfAlgCat.mkQuotient_comp_eqToHom (definingHopfIdeal_eq_special K n)
  have h :=
    ConstantForm.Special.baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom
      (Matrix.map_one (n := Fin n) (algebraMap R K) (map_zero _) (map_one _))
  rw [coordinateMap_def, coordinateMap_def, coordinateHopfAlgebraBaseChangeIso]
  simp only [Iso.trans_hom, eqToIso.hom]
  rw [← CommHopfAlgCat.baseChangeFunctor_map,
    ← eqToHom_map (CommHopfAlgCat.baseChangeFunctor (K := K))
      (coordinateHopfAlgebra_eq_special R n),
    ← Functor.map_comp_assoc, hR]
  rw [CommHopfAlgCat.baseChangeFunctor_map, ← ConstantForm.Special.coordinateMap_def,
    reassoc_of% h, ConstantForm.Special.coordinateMap_def, hK]

/-- The finite-type coordinate Hopf algebra of `SOₙ` commutes with base change. -/
noncomputable def finiteTypeCoordinateHopfAlgebraBaseChangeIso :
    FiniteTypeCommHopfAlgCat.baseChange (K := K) (finiteTypeCoordinateHopfAlgebra R n) ≅
      finiteTypeCoordinateHopfAlgebra K n :=
  eqToIso (congrArg (FiniteTypeCommHopfAlgCat.baseChange (K := K))
      (finiteTypeCoordinateHopfAlgebra_eq_special R n)) ≪≫
    ConstantForm.Special.finiteTypeCoordinateHopfAlgebraBaseChangeIso
      (Matrix.map_one (n := Fin n) (algebraMap R K) (map_zero _) (map_one _)) ≪≫
    eqToIso (finiteTypeCoordinateHopfAlgebra_eq_special K n).symm

/-- The underlying commutative-Hopf-algebra morphism of the finite-type base-change isomorphism
is the coordinate-Hopf-algebra base-change isomorphism, with the object equalities made explicit.
-/
@[simp]
theorem finiteTypeCoordinateHopfAlgebraBaseChangeIso_hom :
    (finiteTypeCoordinateHopfAlgebraBaseChangeIso R K n).hom.hom =
      (eqToIso (congrArg (CommHopfAlgCat.baseChange (K := K))
          (finiteTypeCoordinateHopfAlgebra_obj R n)) ≪≫
        coordinateHopfAlgebraBaseChangeIso R K n ≪≫
        eqToIso (finiteTypeCoordinateHopfAlgebra_obj K n).symm).hom := by
  simp only [finiteTypeCoordinateHopfAlgebraBaseChangeIso, coordinateHopfAlgebraBaseChangeIso,
    Iso.trans_hom, eqToIso.hom, ObjectProperty.FullSubcategory.comp_hom,
    ConstantForm.Special.finiteTypeCoordinateHopfAlgebraBaseChangeIso_hom, Category.assoc,
    ObjectProperty.eqToHom_hom, eqToHom_trans_assoc, eqToHom_trans]

/-- The inverse base-change isomorphism is compatible with the quotient coordinate morphisms. -/
@[reassoc]
theorem coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_inv :
    coordinateMap K n ≫ (coordinateHopfAlgebraBaseChangeIso R K n).inv =
      (GeneralLinear.coordinateHopfAlgebraBaseChangeIso R K n).inv ≫
        CommHopfAlgCat.baseChangeMap (K := K) (coordinateMap R n) := by
  rw [Iso.comp_inv_eq, Category.assoc,
    baseChangeMap_coordinateMap_comp_coordinateHopfAlgebraBaseChangeIso_hom,
    Iso.inv_hom_id_assoc]

end Coordinate

/-! ### Base change of the group scheme -/

section GroupScheme

variable (R K : Type u) [CommRing R] [CommRing K] [Algebra R K] (n : ℕ)

/-- **Base change of `SOₙ`**: the base change to `K` of the special orthogonal group scheme over
`R` is the special orthogonal group scheme over `K`, the Hopf-ideal base-change comparison of
`GLₙ` at the defining Hopf ideals, between the quotient-spectrum presentations
`groupScheme_def`. -/
noncomputable def groupSchemeBaseChangeIso :
    (Over.pullback (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.obj
        (groupScheme R n) ≅ groupScheme K n :=
  (Over.pullback (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.mapIso
      (eqToIso ((groupScheme_def R n).trans (congrArg (CommHopfAlgCat.quotientSpec _)
        (definingHopfIdeal_eq_special R n)))) ≪≫
    ConstantForm.Special.groupSchemeBaseChangeIso
      (Matrix.map_one (n := Fin n) (algebraMap R K) (map_zero _) (map_one _)) ≪≫
    eqToIso ((groupScheme_def K n).trans (congrArg (CommHopfAlgCat.quotientSpec _)
      (definingHopfIdeal_eq_special K n))).symm

/-- The base-change isomorphism of `SOₙ` is the Hopf-ideal base-change comparison of `GLₙ` for
the inverse base-change isomorphism of coordinate Hopf algebras. -/
theorem groupSchemeBaseChangeIso_def :
    groupSchemeBaseChangeIso R K n =
      (Over.pullback (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R K)))).mapGrp.mapIso (eqToIso (groupScheme_def R n)) ≪≫
        GeneralLinear.hopfIdealBaseChangeIso R K n (definingHopfIdeal R n)
          (definingHopfIdeal K n) (coordinateHopfAlgebraBaseChangeIso R K n).symm ≪≫
        eqToIso (groupScheme_def K n).symm := by
  rw [groupSchemeBaseChangeIso, ConstantForm.Special.groupSchemeBaseChangeIso_def,
    coordinateHopfAlgebraBaseChangeIso]
  -- Induct on the two ideal equalities to compare the transported quotient presentations.
  let F := (Over.pullback (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp
  have transport
      {I I' : HopfIdeal R (GeneralLinear.coordinateHopfAlgebra R n)}
      {J J' : HopfIdeal K (GeneralLinear.coordinateHopfAlgebra K n)}
      (hI : I = I') (hJ : J = J')
      (sR : groupScheme R n = CommHopfAlgCat.quotientSpec _ I)
      (sK : groupScheme K n = CommHopfAlgCat.quotientSpec _ J)
      (e : CommHopfAlgCat.baseChange (K := K) (CommHopfAlgCat.quotient _ I') ≅
        CommHopfAlgCat.quotient _ J') :
      F.mapIso (eqToIso (sR.trans (congrArg (CommHopfAlgCat.quotientSpec _) hI))) ≪≫
          GeneralLinear.hopfIdealBaseChangeIso R K n I' J' e.symm ≪≫
          eqToIso (sK.trans (congrArg (CommHopfAlgCat.quotientSpec _) hJ)).symm =
        F.mapIso (eqToIso sR) ≪≫
          GeneralLinear.hopfIdealBaseChangeIso R K n I J
            (eqToIso (congrArg (fun P ↦ CommHopfAlgCat.baseChange (K := K)
              (CommHopfAlgCat.quotient _ P)) hI) ≪≫ e ≪≫
              eqToIso (congrArg (CommHopfAlgCat.quotient _) hJ).symm).symm ≪≫
          eqToIso sK.symm := by
    subst I' J'
    simp
  exact transport (definingHopfIdeal_eq_special R n) (definingHopfIdeal_eq_special K n)
    (groupScheme_def R n) (groupScheme_def K n) _

/-- Followed by the quotient-spectrum presentation `groupScheme_def` over `K`, the base-change
isomorphism of `SOₙ` is the Hopf-ideal base-change comparison of `GLₙ`, after the presentation
over `R`. -/
@[reassoc]
theorem groupSchemeBaseChangeIso_hom_comp_eqToHom :
    (groupSchemeBaseChangeIso R K n).hom ≫ eqToHom (groupScheme_def K n) =
      (Over.pullback (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (algebraMap R K)))).mapGrp.map (eqToHom (groupScheme_def R n)) ≫
        (GeneralLinear.hopfIdealBaseChangeIso R K n (definingHopfIdeal R n)
          (definingHopfIdeal K n) (coordinateHopfAlgebraBaseChangeIso R K n).symm).hom := by
  simp only [groupSchemeBaseChangeIso_def, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom,
    Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

/-- **Base change of `SOₙ` is compatible with the inclusions.** Along the base-change
isomorphisms, the base change of the inclusion of `SOₙ` into `GLₙ` over `R` is the inclusion over
`K`. -/
@[reassoc]
theorem map_inclusion_comp_groupSchemeBaseChangeIso_hom :
    (Over.pullback (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R K)))).mapGrp.map
          (inclusion R n) ≫ (GeneralLinear.groupSchemeBaseChangeIso R K n).hom =
      (groupSchemeBaseChangeIso R K n).hom ≫ inclusion K n := by
  have h := ConstantForm.Special.map_hopfIdealInclusion_comp_groupSchemeBaseChangeIso_hom
    (Matrix.map_one (n := Fin n) (algebraMap R K) (map_zero _) (map_one _))
  have hR := CommHopfAlgCat.eqToHom_comp_quotientSpecι
    (GeneralLinear.coordinateHopfAlgebra R n) (definingHopfIdeal_eq_special R n)
  have hK := CommHopfAlgCat.eqToHom_comp_quotientSpecι
    (GeneralLinear.coordinateHopfAlgebra K n) (definingHopfIdeal_eq_special K n).symm
  rw [inclusion_eq_eqToHom_comp_hopfIdealInclusion, inclusion_eq_eqToHom_comp_hopfIdealInclusion,
    groupSchemeBaseChangeIso]
  rw [GeneralLinear.hopfIdealInclusion_def, ← reassoc_of% hR,
    ← GeneralLinear.hopfIdealInclusion_def, eqToHom_trans_assoc,
    Functor.map_comp, Category.assoc, h]
  simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Category.assoc,
    eqToHom_trans_assoc, GeneralLinear.hopfIdealInclusion_def, reassoc_of% hK]

end GroupScheme

end TauCeti.SpecialOrthogonal
