/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.Homology.Relative.Coefficients
public import TauCeti.AlgebraicTopology.Singular.Relative

/-!
# Changing the category of coefficients of relative singular homology

For an additive functor `F : C ⥤ D` between preadditive categories with homology that preserves
coproducts and homology, `TopPair.singularHomologyObjIso` identifies `F (Hₙ(P; R))` with
`Hₙ(P; F R)` for a topological pair `P`, naturally in `P` and compatible with the quotient map
`TopPair.singularHomologyπ`. This wraps `SSetPair.homologyFunctorObjCompIso` via
`TopPair.toSSetPair`, feeding `TauCeti.AlgebraicTopology.Singular.LocalHomology.Coefficients`.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology Simplicial

universe w v v' u u'

namespace TopPair

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D] [Preadditive C]
  [Preadditive D] [HasCoproducts.{w} C] [HasCoproducts.{w} D] [CategoryWithHomology C]
  [CategoryWithHomology D] (F : C ⥤ D) [F.Additive]
  [∀ T : Type w, PreservesColimitsOfShape (Discrete T) F] [F.PreservesHomology] (R : C)

/-- **Relative singular homology commutes with exact coproduct-preserving `F`**: `F Hₙ ≅ Hₙ F`. -/
def singularHomologyObjIso (P : TopPair.{w}) (n : ℕ) :
    F.obj (P.singularHomology R n) ≅ P.singularHomology (F.obj R) n :=
  (SSetPair.homologyFunctorObjCompIso F R n).app (toSSetPair.obj P)

lemma singularHomologyObjIso_hom (P : TopPair.{w}) (n : ℕ) : (singularHomologyObjIso F R P n).hom =
    (SSetPair.homologyFunctorObjCompIso F R n).hom.app (toSSetPair.obj P) := (rfl)

lemma singularHomologyObjIso_inv (P : TopPair.{w}) (n : ℕ) : (singularHomologyObjIso F R P n).inv =
    (SSetPair.homologyFunctorObjCompIso F R n).inv.app (toSSetPair.obj P) := (rfl)

@[reassoc]
lemma map_singularHomologyMap_comp_singularHomologyObjIso_hom {P P' : TopPair.{w}}
    (f : P ⟶ P') (n : ℕ) :
    F.map (TopPair.singularHomologyMap f R n) ≫ (singularHomologyObjIso F R P' n).hom =
      (singularHomologyObjIso F R P n).hom ≫ TopPair.singularHomologyMap f (F.obj R) n :=
  (SSetPair.homologyFunctorObjCompIso F R n).hom.naturality (toSSetPair.map f)

@[reassoc]
lemma map_singularHomologyπ_comp_singularHomologyObjIso_hom (P : TopPair.{w}) (n : ℕ) :
    F.map (P.singularHomologyπ R n) ≫ (singularHomologyObjIso F R P n).hom =
      (SSet.homologyObjIso F R (TopCat.toSSet.obj P.fst) n).hom ≫ P.singularHomologyπ (F.obj R) n :=
  SSetPair.map_homologyπ_comp_homologyFunctorObjCompIso_hom_app F R n (toSSetPair.obj P)

end TopPair
