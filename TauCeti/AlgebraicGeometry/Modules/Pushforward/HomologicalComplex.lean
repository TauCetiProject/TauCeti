/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
public import TauCeti.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.Additive

/-!
# Direct image and complexes of module sections

The abelian presheaf complex underlying the direct image of a complex of scheme modules is
its source presheaf complex precomposed with inverse image of opens. This identification is
natural in the complex and is the identity in every degree.
-/

public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Functor
open TauCeti.AlgebraicGeometry TauCeti.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The complex of presheaves underlying the direct image of a complex of scheme modules
is the complex of presheaves on the source precomposed with inverse image of opens. -/
def pushforwardSectionsComplexIso :
    (Scheme.Modules.pushforward f ⋙ toSheaf Y).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        (sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _ ≅
    (toSheaf X).mapHomologicalComplex _ ⋙
      (sheafToPresheaf _ AddCommGrpCat.{u}).mapHomologicalComplex _ ⋙
        ((whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
          (Opens.map f.base).op).mapHomologicalComplex _ :=
  -- The composite presentation exposes the zero-preservation instances of each functor.
  NatIso.mapHomologicalComplex
    (F := (Scheme.Modules.pushforward f ⋙ toSheaf Y) ⋙
      sheafToPresheaf _ AddCommGrpCat.{u})
    (G := (toSheaf X ⋙ sheafToPresheaf _ AddCommGrpCat.{u}) ⋙
      (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
        (Opens.map f.base).op)
    (pushforwardCompToPresheafIso f) _

/-- The direct-image comparison is the identity on each term of the presheaf complex. -/
@[simp]
lemma pushforwardSectionsComplexIso_hom_app_f (K : CochainComplex X.Modules ℕ) (n : ℕ) :
    ((f.pushforwardSectionsComplexIso).hom.app K).f n = 𝟙 _ := by
  exact (NatIso.mapHomologicalComplex_hom_app_f
    (F := (Scheme.Modules.pushforward f ⋙ toSheaf Y) ⋙
      sheafToPresheaf _ AddCommGrpCat.{u})
    (G := (toSheaf X ⋙ sheafToPresheaf _ AddCommGrpCat.{u}) ⋙
      (whiskeringLeft Y.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{u}).obj
        (Opens.map f.base).op)
    (pushforwardCompToPresheafIso f) _ K n).trans
    (pushforwardCompToPresheafIso_hom_app f (K.X n))

/-- The inverse direct-image comparison is the identity on each term of the presheaf complex. -/
@[simp]
lemma pushforwardSectionsComplexIso_inv_app_f (K : CochainComplex X.Modules ℕ) (n : ℕ) :
    ((f.pushforwardSectionsComplexIso).inv.app K).f n = 𝟙 _ := by
  exact (Iso.inv_eq_inv
    ((HomologicalComplex.eval (Y.Opensᵒᵖ ⥤ AddCommGrpCat.{u}) (ComplexShape.up ℕ) n).mapIso
      ((f.pushforwardSectionsComplexIso).app K))
    (Iso.refl _)).2 (f.pushforwardSectionsComplexIso_hom_app_f K n)

end AlgebraicGeometry.Scheme.Hom
