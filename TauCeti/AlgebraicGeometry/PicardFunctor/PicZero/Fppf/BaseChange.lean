/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.BaseChange
public import TauCeti.AlgebraicGeometry.PicardFunctor.PicZero.Fppf
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Over

/-!
# Base change of the degree-zero Picard fppf sheaf

For a smooth proper geometrically connected family of curves, formation of the degree-zero
Picard fppf sheaf commutes with arbitrary base change. The comparison is the sheafification
of `relativePicardDegreeZeroFunctorBaseChangeIso`. Restriction along `Over.map` commutes with
sheafification because this functor is both continuous and cocontinuous.

The comparison respects the canonical maps from degree-zero Picard classes. If an `S`-scheme
represents the degree-zero Picard fppf sheaf, its base change represents the sheaf of the
base-changed family. This does not assume a section of the family or construct a representing
scheme.

## References

* S. Kleiman, *The Picard scheme*, in *Fundamental Algebraic Geometry: Grothendieck's FGA
  Explained*, Exercises 4.4 and 6.21.
-/

public section

open CategoryTheory Limits

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {S S' X : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
variable [IsProper f] [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f]

/-- The base-change comparison of degree-zero Picard presheaves in additive notation. -/
def relativePicardDegreeZeroAddPresheafBaseChangeIso :
    relativePicardDegreeZeroAddPresheaf (pullback.fst g f) ≅
      (Over.map g).op ⋙ relativePicardDegreeZeroAddPresheaf f :=
  eqToIso (relativePicardDegreeZeroAddPresheaf_eq _) ≪≫
    Functor.isoWhiskerRight (relativePicardDegreeZeroFunctorBaseChangeIso f g)
      CommGrpCat.toAddCommGrp ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Over.map g).op
      (eqToIso (relativePicardDegreeZeroAddPresheaf_eq f).symm)

/-- The additive comparison sends a native degree-zero Picard class to its native base-change
comparison, expressed in additive notation. -/
@[simp]
theorem relativePicardDegreeZeroAddPresheafBaseChangeIso_hom_app_addEquiv_ofMul
    {T : (Over S')ᵒᵖ} (c : (relativePicardDegreeZeroFunctor (pullback.fst g f)).obj T) :
    ConcreteCategory.hom (C := AddCommGrpCat.{u + 1})
        (X := (relativePicardDegreeZeroAddPresheaf (pullback.fst g f)).obj T)
        (Y := (relativePicardDegreeZeroAddPresheaf f).obj (.op ((Over.map g).obj T.unop)))
        ((relativePicardDegreeZeroAddPresheafBaseChangeIso f g).hom.app T)
        (relativePicardDegreeZeroAddPresheafAddEquiv (pullback.fst g f) T (Additive.ofMul c)) =
      relativePicardDegreeZeroAddPresheafAddEquiv f ((Over.map g).op.obj T)
        (Additive.ofMul ((relativePicardDegreeZeroFunctorBaseChangeIso f g).hom.app T c)) := by
  simp only [relativePicardDegreeZeroAddPresheafBaseChangeIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    eqToIso.hom, NatTrans.comp_app, AddCommGrpCat.comp_apply]
  simp only [eqToHom_app]
  erw [relativePicardDegreeZeroAddPresheaf_eqToHom_app_addEquiv]
  -- The additive functor applies the same group homomorphism, and associator components
  -- are identities; evaluate them before the inverse presentation transport.
  change ConcreteCategory.hom (C := AddCommGrpCat)
      (eqToHom (Functor.congr_obj (relativePicardDegreeZeroAddPresheaf_eq f).symm
        ((Over.map g).op.obj T))) (Additive.ofMul
        ((relativePicardDegreeZeroFunctorBaseChangeIso f g).hom.app T c)) = _
  exact relativePicardDegreeZeroAddPresheaf_eqToHom_symm_app f _ _

/-- Formation of the degree-zero Picard fppf sheaf commutes with arbitrary base change. -/
def relativePicardDegreeZeroFppfSheafBaseChangeIso :
    relativePicardDegreeZeroFppfSheaf (pullback.fst g f) ≅
      ((Over.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).obj
          (relativePicardDegreeZeroFppfSheaf f) :=
  eqToIso (relativePicardDegreeZeroFppfSheaf_eq _) ≪≫
    (presheafToSheaf (Scheme.fppfTopology.over S') AddCommGrpCat.{u + 1}).mapIso
      (relativePicardDegreeZeroAddPresheafBaseChangeIso f g) ≪≫
    ((Over.map g).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).app
        (relativePicardDegreeZeroAddPresheaf f) ≪≫
    ((Over.map g).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).mapIso
        (eqToIso (relativePicardDegreeZeroFppfSheaf_eq f).symm)

/-- After identifying the source with its sheafification, the comparison is the sheafified
presheaf comparison followed by the pushforward comparison and the target identification. -/
private theorem relativePicardDegreeZeroFppfSheafBaseChangeIso_hom_eq :
    eqToHom (relativePicardDegreeZeroFppfSheaf_obj (pullback.fst g f)).symm ≫
        (relativePicardDegreeZeroFppfSheafBaseChangeIso f g).hom.hom =
      sheafifyMap (Scheme.fppfTopology.over S')
          (relativePicardDegreeZeroAddPresheafBaseChangeIso f g).hom ≫
        (((Over.map g).pushforwardContinuousSheafificationCompatibility AddCommGrpCat.{u + 1}
          (Scheme.fppfTopology.over S') (Scheme.fppfTopology.over S)).hom.app
            (relativePicardDegreeZeroAddPresheaf f)).hom ≫
        Functor.whiskerLeft (Over.map g).op
          (eqToHom (relativePicardDegreeZeroFppfSheaf_obj f).symm) := by
  simp only [relativePicardDegreeZeroFppfSheafBaseChangeIso, Iso.trans_hom,
    Functor.mapIso_hom, eqToIso.hom, ObjectProperty.FullSubcategory.comp_hom]
  simp only [← ObjectProperty.ι_map, eqToHom_map, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp, sheafifyMap]
  congr 2
  exact (eqToHom_map ((Functor.whiskeringLeft _ _ _).obj (Over.map g).op) _).symm

/-- The sheaf comparison sends the image of a degree-zero Picard class to the image of its
base-change comparison. -/
@[reassoc (attr := simp)]
theorem relativePicardDegreeZeroToFppfSheaf_comp_baseChangeIso_hom :
    relativePicardDegreeZeroToFppfSheaf (pullback.fst g f) ≫
        (relativePicardDegreeZeroFppfSheafBaseChangeIso f g).hom.hom =
      (relativePicardDegreeZeroAddPresheafBaseChangeIso f g).hom ≫
        Functor.whiskerLeft (Over.map g).op (relativePicardDegreeZeroToFppfSheaf f) := by
  rw [relativePicardDegreeZeroToFppfSheaf_eq, Category.assoc,
    relativePicardDegreeZeroFppfSheafBaseChangeIso_hom_eq, relativePicardDegreeZeroToFppfSheaf_eq,
    Functor.whiskerLeft_comp]
  -- The underlying presheaf of the pushforward sheaf is `(Over.map g).op ⋙ _` only after
  -- unfolding `sheafPushforwardContinuous`, so the compatibility applies by `exact`, not `rw`.
  exact Functor.toSheafify_comp_sheafifyMap_comp_sheafificationCompatibility_hom_assoc _ _ _ _ _ _

/-- On actual degree-zero Picard classes, the sheaf comparison is induced by the presheaf
comparison. -/
@[simp]
theorem relativePicardDegreeZeroFppfSheafBaseChangeIso_hom_app_toFppfSheaf
    {T : (Over S')ᵒᵖ} (c : (relativePicardDegreeZeroAddPresheaf (pullback.fst g f)).obj T) :
    (relativePicardDegreeZeroFppfSheafBaseChangeIso f g).hom.hom.app T
        ((relativePicardDegreeZeroToFppfSheaf (pullback.fst g f)).app T c) =
      (relativePicardDegreeZeroToFppfSheaf f).app ((Over.map g).op.obj T)
        ((relativePicardDegreeZeroAddPresheafBaseChangeIso f g).hom.app T c) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (relativePicardDegreeZeroToFppfSheaf_comp_baseChangeIso_hom f g) T) c

/-- A scheme representing the degree-zero Picard fppf sheaf base changes to a scheme
representing that sheaf for the base-changed family. -/
def relativePicardDegreeZeroFppfSheafBaseChangeRepresentableBy {P : Over S}
    (e : ((relativePicardDegreeZeroFppfSheaf f).obj ⋙
      forget AddCommGrpCat).RepresentableBy P) :
    ((relativePicardDegreeZeroFppfSheaf (pullback.fst g f)).obj ⋙
      forget AddCommGrpCat).RepresentableBy ((Over.pullback g).obj P) :=
  ((Over.mapPullbackAdj g).representableByComp e).ofIso
    ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        ((sheafToPresheaf (Scheme.fppfTopology.over S') AddCommGrpCat.{u + 1}).mapIso
          (relativePicardDegreeZeroFppfSheafBaseChangeIso f g)).symm _)

/-- The base-changed representation is obtained from the original representation by the
`Over.map`–`Over.pullback` adjunction and the canonical Picard sheaf comparison. -/
@[simp]
theorem relativePicardDegreeZeroFppfSheafBaseChangeRepresentableBy_homEquiv
    {P : Over S}
    (e : ((relativePicardDegreeZeroFppfSheaf f).obj ⋙
      forget AddCommGrpCat).RepresentableBy P) {T : Over S'}
    (φ : T ⟶ (Over.pullback g).obj P) :
    dsimp% only [Functor.comp_obj]
      ((relativePicardDegreeZeroFppfSheafBaseChangeIso f g).hom.hom.app (.op T)
        ((relativePicardDegreeZeroFppfSheafBaseChangeRepresentableBy f g e).homEquiv φ)) =
      e.homEquiv (((Over.mapPullbackAdj g).homEquiv T P).symm φ) := by
  simp only [relativePicardDegreeZeroFppfSheafBaseChangeRepresentableBy,
    Functor.RepresentableBy.ofIso, Equiv.trans_apply,
    Adjunction.representableByComp_homEquiv_apply]
  -- The associator components are identities. Forgetting the sheaf comparison leaves its
  -- inverse applied to the represented class.
  change (relativePicardDegreeZeroFppfSheafBaseChangeIso f g).hom.hom.app (.op T)
      ((relativePicardDegreeZeroFppfSheafBaseChangeIso f g).inv.hom.app (.op T)
        (e.homEquiv (((Over.mapPullbackAdj g).homEquiv T P).symm φ))) = _
  exact Iso.inv_hom_id_app_apply
    ((sheafToPresheaf (Scheme.fppfTopology.over S') AddCommGrpCat.{u + 1}).mapIso
      (relativePicardDegreeZeroFppfSheafBaseChangeIso f g)) _ _

end

end TauCeti.AlgebraicGeometry
