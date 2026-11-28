/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeSpec.Basic

/-!
# Extending the sections of a commutative algebra from the affine site

`AlgebraicGeometry.Scheme.sectionsSheafFunctor` sends a commutative algebra in scheme modules
to its sheaf of section rings under the structure sheaf. The restriction of its structure map
to the small affine Zariski site is the map used in `CommMon.coequifibered_toSectionsPresheaf`.

`AlgebraicGeometry.Scheme.sectionsPresheafIso` identifies the extension of that restriction with
the original sheaf of algebras, naturally in the algebra. It uses Mathlib's
`Scheme.AffineZariskiSite.sheafEquiv` and `Under.postEquiv`.

## References

* The Stacks Project, Situation 27.3.1 (01LM).
* The Stacks Project, Lemma 27.3.2 (01LN).
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

open AffineZariskiSite

noncomputable section

/-- Restriction to the small affine Zariski site is an equivalence for sheaves of
commutative algebras under the structure sheaf. The inverse extends the sheaf and its
structure map to all opens. -/
abbrev affineAlgebraSheafEquiv (X : Scheme.{u}) :
    Under X.sheaf ≌ Under ((sheafEquiv (X := X) (A := CommRingCat.{u})).inverse.obj X.sheaf) :=
  Under.postEquiv X.sheaf (sheafEquiv (X := X) (A := CommRingCat.{u})).symm

/-- The sheaf of section rings of a commutative algebra, equipped with its structure map
from the structure sheaf. -/
def sectionsSheafFunctor (X : Scheme.{u}) : CommMon X.Modules ⥤ Under X.sheaf :=
  let F : CommMon X.Modules ⥤ TopCat.Sheaf CommRingCat.{u} X :=
    { obj := fun A ↦ ⟨A.sectionsPresheaf, A.isSheaf_sectionsPresheaf⟩
      map := fun f ↦ ⟨CommMon.sectionsPresheafMap f⟩
      map_id := fun A ↦ Sheaf.hom_ext (CommMon.sectionsPresheafMap_id A)
      map_comp := fun f g ↦ Sheaf.hom_ext (CommMon.sectionsPresheafMap_comp f g) }
  F.toUnder X.sheaf (fun A ↦ ⟨A.toSectionsPresheaf⟩)
    (fun f ↦ Sheaf.hom_ext (CommMon.toSectionsPresheaf_comp_sectionsPresheafMap f))

variable {X : Scheme.{u}}

/-- The section sheaf has the section rings and restriction maps of the given algebra. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsSheafFunctor_obj_right_obj (A : CommMon X.Modules) :
    ((sectionsSheafFunctor X).obj A).right.obj = A.sectionsPresheaf :=
  (rfl)

/-- The structure map of the section sheaf is induced by the unit of the algebra. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsSheafFunctor_obj_hom_hom (A : CommMon X.Modules) :
    ((sectionsSheafFunctor X).obj A).hom.hom ≫
        eqToHom A.sectionsSheafFunctor_obj_right_obj = A.toSectionsPresheaf :=
  (rfl)

/-- On the underlying presheaves, the section sheaf functor applies the given map to sections. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsSheafFunctor_map_right_hom
    {A B : CommMon X.Modules} (f : A ⟶ B) :
    ((sectionsSheafFunctor X).map f).right.hom ≫ eqToHom B.sectionsSheafFunctor_obj_right_obj =
      eqToHom A.sectionsSheafFunctor_obj_right_obj ≫ CommMon.sectionsPresheafMap f :=
  (rfl)

/-- Restricting the algebra's structure map to affine opens gives the natural transformation
used to glue its relative spectrum when the algebra is quasi-coherent. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsSheafFunctor_affine_obj_hom_hom
    (A : CommMon X.Modules) :
    (X.affineAlgebraSheafEquiv.functor.obj ((sectionsSheafFunctor X).obj A)).hom.hom ≫
      (toOpensFunctor X).op.whiskerLeft (eqToHom A.sectionsSheafFunctor_obj_right_obj) =
        (toOpensFunctor X).op.whiskerLeft A.toSectionsPresheaf :=
  (rfl)

/-- Extending the affine restriction of the section sheaf back to the Zariski site recovers
the original sheaf of algebras. The isomorphism is natural in the algebra and commutes with
the maps from the structure sheaf. -/
def sectionsPresheafIso (X : Scheme.{u}) :
    sectionsSheafFunctor X ⋙
      (X.affineAlgebraSheafEquiv.functor ⋙ X.affineAlgebraSheafEquiv.inverse) ≅
    sectionsSheafFunctor X :=
  Functor.isoWhiskerLeft _ X.affineAlgebraSheafEquiv.unitIso.symm ≪≫
    Functor.rightUnitor _

/-- The forward comparison is the inverse unit of affine restriction on sheaves of
algebras. -/
@[simp]
lemma _root_.CategoryTheory.CommMon.sectionsPresheafIso_hom_app (A : CommMon X.Modules) :
    (sectionsPresheafIso X).hom.app A =
      X.affineAlgebraSheafEquiv.unitIso.inv.app ((sectionsSheafFunctor X).obj A) :=
  (rfl)

end

end AlgebraicGeometry.Scheme
