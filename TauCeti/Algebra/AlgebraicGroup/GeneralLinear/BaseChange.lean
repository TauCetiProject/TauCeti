/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Coordinate.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Scheme
public import TauCeti.AlgebraicGeometry.AffineGroupScheme.BaseChange.Coordinate

/-!
# Base change of the general linear group scheme

The scheme-theoretic base change of `GL_n` along a morphism of commutative rings is canonically
isomorphic to the general linear group scheme constructed directly over the target ring. This is
the scheme-side form of `GeneralLinear.coordinateHopfAlgebraBaseChangeIso`.

## Main declarations

* `TauCeti.GeneralLinear.groupSchemeBaseChangeIso`: the canonical base-change isomorphism for
  general linear group schemes.
* `TauCeti.GeneralLinear.hopfIdealBaseChangeIso`: the corresponding comparison for a closed
  subgroup presented by compatible Hopf ideals before and after base change.
-/

public section

open AlgebraicGeometry CategoryTheory

namespace TauCeti.GeneralLinear

universe u

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (n : ℕ)

/-- The canonical identification of the base change of `GL_n/R` with `GL_n/S`. -/
noncomputable def groupSchemeBaseChangeIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
        (groupScheme R n) ≅ groupScheme S n :=
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.mapIso
      (eqToIso (groupScheme_def R n)) ≪≫
    AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso
      (coordinateHopfAlgebra R n) ≪≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of S)).mapIso
      (coordinateHopfAlgebraBaseChangeIso R S n).symm.op ≪≫
    eqToIso (groupScheme_def S n).symm

/-! ## Closed subgroups under base change -/

/-- The base change of the Hopf spectrum of the coordinate algebra of `GL_n/R`, expressed as the
Hopf spectrum of the coordinate algebra constructed directly over `S`. -/
noncomputable def coordinateGroupSchemeBaseChangeIso :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
        ((AlgebraicGeometry.hopfSpec (CommRingCat.of R)).obj
          (Opposite.op (coordinateHopfAlgebra R n))) ≅
      (AlgebraicGeometry.hopfSpec (CommRingCat.of S)).obj
        (Opposite.op (coordinateHopfAlgebra S n)) :=
  AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso (coordinateHopfAlgebra R n) ≪≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of S)).mapIso
      (coordinateHopfAlgebraBaseChangeIso R S n).symm.op

/-- The forward base-change comparison is the coordinate-presentation comparison, preceded and
followed by the named presentations of the source and target general linear group schemes. -/
theorem groupSchemeBaseChangeIso_hom :
    (groupSchemeBaseChangeIso R S n).hom =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.map
          (eqToHom (groupScheme_def R n)) ≫
        (coordinateGroupSchemeBaseChangeIso R S n).hom ≫
        eqToHom (groupScheme_def S n).symm := by
  rfl

/-- The base change of a closed subgroup presented by a Hopf ideal, transported to a compatible
quotient presentation over the target ring. -/
noncomputable def hopfIdealBaseChangeIso
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (I' : HopfIdeal S (coordinateHopfAlgebra S n))
    (e : CommHopfAlgCat.quotient (coordinateHopfAlgebra S n) I' ≅
      CommHopfAlgCat.baseChange (K := S)
        (CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I)) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.obj
        (CommHopfAlgCat.quotientSpec (coordinateHopfAlgebra R n) I) ≅
      CommHopfAlgCat.quotientSpec (coordinateHopfAlgebra S n) I' :=
  AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso
      (CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I) ≪≫
    (AlgebraicGeometry.hopfSpec (CommRingCat.of S)).mapIso e.op

/-- A compatible quotient presentation identifies the base change of a closed-subgroup
inclusion with the closed-subgroup inclusion over the target ring. -/
theorem map_quotientSpecι_comp_coordinateGroupSchemeBaseChangeIso
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (I' : HopfIdeal S (coordinateHopfAlgebra S n))
    (e : CommHopfAlgCat.quotient (coordinateHopfAlgebra S n) I' ≅
      CommHopfAlgCat.baseChange (K := S)
        (CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I))
    (he : CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra S n) I' ≫ e.hom =
      (coordinateHopfAlgebraBaseChangeIso R S n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R n) I)) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.map
          (CommHopfAlgCat.quotientSpecι (coordinateHopfAlgebra R n) I) ≫
        (coordinateGroupSchemeBaseChangeIso R S n).hom =
      (hopfIdealBaseChangeIso R S n I I' e).hom ≫
        CommHopfAlgCat.quotientSpecι (coordinateHopfAlgebra S n) I' := by
  rw [coordinateGroupSchemeBaseChangeIso, hopfIdealBaseChangeIso]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [CommHopfAlgCat.quotientSpecι_def, ← Category.assoc,
    AffineGroupSchemeCat.hopfSpecBaseChangeGrpIso_hom_naturality]
  simp only [Category.assoc]
  rw [cancel_epi]
  rw [CommHopfAlgCat.quotientSpecι_def, ← Functor.map_comp]
  conv_rhs => rw [← Functor.map_comp]
  simp only [Iso.op_hom, Iso.symm_hom]
  rw [← op_comp, ← op_comp, he]

/-- Base change carries a Hopf-ideal closed immersion into `GL_n/R` to the compatible
Hopf-ideal closed immersion into `GL_n/S`. -/
theorem map_hopfIdealInclusion_comp_groupSchemeBaseChangeIso
    (I : HopfIdeal R (coordinateHopfAlgebra R n))
    (I' : HopfIdeal S (coordinateHopfAlgebra S n))
    (e : CommHopfAlgCat.quotient (coordinateHopfAlgebra S n) I' ≅
      CommHopfAlgCat.baseChange (K := S)
        (CommHopfAlgCat.quotient (coordinateHopfAlgebra R n) I))
    (he : CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra S n) I' ≫ e.hom =
      (coordinateHopfAlgebraBaseChangeIso R S n).inv ≫
        CommHopfAlgCat.baseChangeMap
          (CommHopfAlgCat.mkQuotient (coordinateHopfAlgebra R n) I)) :
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapGrp.map
          (hopfIdealInclusion R n I) ≫
        (groupSchemeBaseChangeIso R S n).hom =
      (hopfIdealBaseChangeIso R S n I I' e).hom ≫
        hopfIdealInclusion S n I' := by
  have hI : hopfIdealInclusion R n I ≫
      eqToHom (groupScheme_def R n) =
      CommHopfAlgCat.quotientSpecι (coordinateHopfAlgebra R n) I := by
    rw [← eqToIso.hom, hopfIdealInclusion_def, Category.assoc]
    simp
  rw [groupSchemeBaseChangeIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, hI]
  rw [← Category.assoc]
  rw [map_quotientSpecι_comp_coordinateGroupSchemeBaseChangeIso R S n I I' e he]
  rw [hopfIdealInclusion_def, eqToIso.hom]
  simp only [Category.assoc]

end TauCeti.GeneralLinear
