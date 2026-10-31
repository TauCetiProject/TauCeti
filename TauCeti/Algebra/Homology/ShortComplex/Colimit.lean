/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology and exact colimits

This file proves that homology of short complexes in an abelian category, and hence homology of
homological complexes, commutes with colimits of every shape whose colimits are exact.

## Main results

* `TauCeti.shortComplexHomologyFunctor_preservesColimitsOfShape`: homology of short complexes
  preserves colimits of any exact shape.
* `TauCeti.homologicalComplexShortComplexFunctor_preservesColimitsOfShape`: the short complex
  associated to a homological complex preserves all existing colimits.
* `TauCeti.homologicalComplexHomologyFunctor_preservesColimitsOfShape`: homology of homological
  complexes preserves colimits of any exact shape.

## Implementation notes

A diagram `F : J ⥤ ShortComplex C` corresponds under `ShortComplex.functorEquivalence` to a short
complex `S` of diagrams, and the colimit cocone used here is the image of `S` under
`colim : (J ⥤ C) ⥤ C`, with legs assembled from the counit of that equivalence. Working with the
counit rather than with the definitional identification of the two presentations keeps every
intermediate statement well typed for `rw` and `simp`: in a general category, unlike in a concrete
one, neither the unit laws nor associativity hold definitionally, so the composites appearing here
cannot be manipulated by `rfl` alone.

Exactness of `J`-shaped colimits makes `colim` preserve homology, which turns the homology of that
cocone into the chosen colimit of the pointwise homology diagram.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe w w' u' v'

variable {C : Type u'} [Category.{v'} C] [Abelian C]
variable {J : Type w} [Category.{w'} J] [HasColimitsOfShape J C]

private theorem mapNatTrans_evaluation_comp_colim
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans
          ((evaluation J C).map f) ≫
        ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (colim.ι Y) =
      ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (colim.ι X) := by
  ext <;>
    simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
      ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃,
      evaluation_map_app, colim.ι_app] <;>
    exact colimit.w _ f

/-- The cocone on `F : J ⥤ ShortComplex C` obtained by applying `colim` to the associated short
complex of diagrams. -/
private noncomputable def shortComplexColimCocone (F : J ⥤ ShortComplex C) : Cocone F where
  pt := ((ShortComplex.functorEquivalence J C).inverse.obj F).map colim
  ι :=
    { app := fun j ↦ (ShortComplex.diagramEvaluationIso F j).inv ≫
        ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (colim.ι j)
      naturality := fun _ _ f ↦ by
        dsimp
        rw [Category.comp_id, ← Category.assoc,
          ShortComplex.diagramEvaluationIso_inv_naturality, Category.assoc,
          mapNatTrans_evaluation_comp_colim] }

/-- The cocone `shortComplexColimCocone F` is colimiting: each of its three components is the
chosen colimit cocone of the corresponding diagram in `C`, up to the identities contributed by the
counit of `ShortComplex.functorEquivalence`. -/
private noncomputable def isColimitShortComplexColimCocone (F : J ⥤ ShortComplex C) :
    IsColimit (shortComplexColimCocone F) :=
  ShortComplex.isColimitOfIsColimitπ _
    (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ ShortComplex.π₁))
      (Cocone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexColimCocone, ShortComplex.π₁]
        rw [ShortComplex.diagramEvaluationIso_inv_τ₁]
        exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ ShortComplex.π₂))
      (Cocone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexColimCocone, ShortComplex.π₂]
        rw [ShortComplex.diagramEvaluationIso_inv_τ₂]
        exact (Category.comp_id _).trans (Category.id_comp _).symm))
    (IsColimit.ofIsoColimit (colimit.isColimit (F ⋙ ShortComplex.π₃))
      (Cocone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexColimCocone, ShortComplex.π₃]
        rw [ShortComplex.diagramEvaluationIso_inv_τ₃]
        exact (Category.comp_id _).trans (Category.id_comp _).symm))

variable [HasExactColimitsOfShape J C]

private theorem shortComplex_mapHomologyIso_colimit (F : J ⥤ ShortComplex C) (j : J) :
    (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).hom ≫
        colimit.ι ((ShortComplex.functorEquivalence J C).inverse.obj F).homology j ≫
          (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso colim).inv =
      ShortComplex.homologyMap
        (((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (colim.ι j)) := by
  -- Since `(colim.ι j).app G = colimit.ι G j`, the coprojection on the left is the component of
  -- `NatTrans.app_homology (colim.ι j)` on `(ShortComplex.functorEquivalence J C).inverse.obj F`.
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq, Category.assoc]
  exact NatTrans.app_homology (colim.ι j)
    ((ShortComplex.functorEquivalence J C).inverse.obj F)

private theorem shortComplexHomologyColimit_compatibility
    (F : J ⥤ ShortComplex C) (j : J) :
    ((ShortComplex.homologyMap (ShortComplex.diagramEvaluationIso F j).inv ≫
            (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso
              ((evaluation J C).obj j)).hom) ≫
          colimit.ι ((ShortComplex.functorEquivalence J C).inverse.obj F).homology j) ≫
        (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso colim).inv =
      ShortComplex.homologyMap ((ShortComplex.diagramEvaluationIso F j).inv ≫
        ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (colim.ι j)) := by
  rw [Category.assoc, Category.assoc, shortComplex_mapHomologyIso_colimit,
    ShortComplex.homologyMap_comp]

/-- Homology of the colimit cocone `shortComplexColimCocone F` is the chosen colimit of the
pointwise homology diagram of `F`. -/
private noncomputable def shortComplexHomologyColimitCoconeIso (F : J ⥤ ShortComplex C) :
    (Cocone.precompose (ShortComplex.homologyDiagramIso F).hom).obj
        (colimit.cocone ((ShortComplex.functorEquivalence J C).inverse.obj F).homology) ≅
      (ShortComplex.homologyFunctor C).mapCocone (shortComplexColimCocone F) :=
  Cocone.ext (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso colim).symm
    (fun j ↦ by
      dsimp [shortComplexColimCocone, ShortComplex.homologyFunctor]
      rw [ShortComplex.homologyDiagramIso_hom_app, shortComplexHomologyColimit_compatibility])

/-- Homology of short complexes preserves colimits of any exact shape. -/
instance shortComplexHomologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J (ShortComplex.homologyFunctor C) where
  preservesColimit {F} :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitShortComplexColimCocone F)
      ((IsColimit.equivOfNatIsoOfIso
        (ShortComplex.homologyDiagramIso F).symm
        (colimit.cocone ((ShortComplex.functorEquivalence J C).inverse.obj F).homology)
        ((ShortComplex.homologyFunctor C).mapCocone (shortComplexColimCocone F))
        (shortComplexHomologyColimitCoconeIso F)) (colimit.isColimit _))

variable {I D : Type*} [Category D] [HasZeroMorphisms D] [HasColimitsOfShape J D]
  (c : ComplexShape I) (q : I)

/-- Sending a homological complex to its short complex at one degree preserves all existing
colimits. -/
instance homologicalComplexShortComplexFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      (HomologicalComplex.shortComplexFunctor D c q) where
  preservesColimit {F} := by
    apply preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval D c (c.prev q))
        (colimit.isColimit F)
    · exact isColimitOfPreserves (HomologicalComplex.eval D c q)
        (colimit.isColimit F)
    · exact isColimitOfPreserves (HomologicalComplex.eval D c (c.next q))
        (colimit.isColimit F)

/-- Homology in any degree of a homological complex preserves colimits of any exact shape. -/
instance homologicalComplexHomologyFunctor_preservesColimitsOfShape :
    PreservesColimitsOfShape J
      (HomologicalComplex.homologyFunctor C c q) := by
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso C c q).symm

end TauCeti
