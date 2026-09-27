/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Homology and exact limits

This file proves that homology of short complexes, and hence homology of homological complexes,
commutes with limits of every shape whose limits are exact.

## Main results

* `TauCeti.shortComplexHomologyFunctor_preservesLimitsOfShape`: homology of short complexes
  preserves limits of any exact shape.
* `TauCeti.homologicalComplexShortComplexFunctor_preservesLimitsOfShape`: the short complex
  associated to a homological complex preserves all existing limits.
* `TauCeti.homologicalComplexHomologyFunctor_preservesLimitsOfShape`: homology of homological
  complexes preserves limits of any exact shape.

## Implementation notes

A diagram `F : J ⥤ ShortComplex C` corresponds under `ShortComplex.functorEquivalence` to a short
complex `S` of diagrams. The limiting cone used here is the image of `S` under
`lim : (J ⥤ C) ⥤ C`, with legs assembled from the counit of that equivalence. Exactness of
`J`-shaped limits makes `lim` preserve homology, identifying the homology of this cone with the
chosen limit of the pointwise homology diagram.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {J : Type w} [Category.{w} J] [HasLimitsOfShape J C]
  [HasExactLimitsOfShape J C]

private noncomputable abbrev shortComplexDiagram
    (F : J ⥤ ShortComplex C) : ShortComplex (J ⥤ C) :=
  (ShortComplex.functorEquivalence J C).inverse.obj F

omit [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] in
/-- Evaluating the short complex of diagrams attached to `F` at `j` gives back `F.obj j`. -/
private noncomputable def shortComplexDiagramEvaluationIso
    (F : J ⥤ ShortComplex C) (j : J) :
    (shortComplexDiagram F).map ((evaluation J C).obj j) ≅ F.obj j :=
  ((ShortComplex.functorEquivalence J C).counitIso.app F).app j

omit [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] in
private theorem shortComplexDiagramEvaluationIso_inv_naturality
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    F.map f ≫ (shortComplexDiagramEvaluationIso F Y).inv =
      (shortComplexDiagramEvaluationIso F X).inv ≫
        (shortComplexDiagram F).mapNatTrans ((evaluation J C).map f) :=
  ((ShortComplex.functorEquivalence J C).counitIso.app F).inv.naturality f

/-- The componentwise limit cone on `F : J ⥤ ShortComplex C`. -/
private noncomputable def shortComplexLimCone (F : J ⥤ ShortComplex C) : Cone F :=
  ShortComplex.limitCone F

/-- The cone `shortComplexLimCone F` is limiting, componentwise. -/
private noncomputable def isLimitShortComplexLimCone (F : J ⥤ ShortComplex C) :
    IsLimit (shortComplexLimCone F) :=
  ShortComplex.isLimitLimitCone F

omit [HasLimitsOfShape J C] [HasExactLimitsOfShape J C] in
private theorem mapHomologyIso_evaluation_naturality
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    ShortComplex.homologyMap
          ((shortComplexDiagram F).mapNatTrans ((evaluation J C).map f)) ≫
        ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj Y)).hom =
      ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj X)).hom ≫
        (shortComplexDiagram F).homology.map f := by
  have h : ShortComplex.homologyMap
        ((shortComplexDiagram F).mapNatTrans ((evaluation J C).map f)) ≫
      ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj Y)).hom =
      ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj X)).hom ≫
        ((evaluation J C).map f).app (shortComplexDiagram F).homology := by
    rw [NatTrans.app_homology ((evaluation J C).map f) (shortComplexDiagram F)]
    simp
  exact h

/-- The pointwise homology diagram of `F` is the homology of the associated short complex of
diagrams. -/
private noncomputable def shortComplexHomologyDiagramIso (F : J ⥤ ShortComplex C) :
    F ⋙ ShortComplex.homologyFunctor C ≅ (shortComplexDiagram F).homology :=
  NatIso.ofComponents
    (fun j ↦ ShortComplex.homologyMapIso (shortComplexDiagramEvaluationIso F j).symm ≪≫
      (shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j))
    (fun {X Y} f ↦ by
      have h : ShortComplex.homologyMap (F.map f) ≫
            (ShortComplex.homologyMap (shortComplexDiagramEvaluationIso F Y).inv ≫
              ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj Y)).hom) =
          (ShortComplex.homologyMap (shortComplexDiagramEvaluationIso F X).inv ≫
              ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj X)).hom) ≫
            (shortComplexDiagram F).homology.map f := by
        rw [Category.assoc, ← mapHomologyIso_evaluation_naturality, ← Category.assoc,
          ← Category.assoc, ← ShortComplex.homologyMap_comp, ← ShortComplex.homologyMap_comp,
          shortComplexDiagramEvaluationIso_inv_naturality]
      exact h)

private theorem shortComplex_mapHomologyIso_limit (F : J ⥤ ShortComplex C) (j : J) :
    ((shortComplexDiagram F).mapHomologyIso lim).inv ≫
        ShortComplex.homologyMap ((shortComplexDiagram F).mapNatTrans (lim.π j)) =
      limit.π (shortComplexDiagram F).homology j ≫
        ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j)).inv := by
  rw [← cancel_mono
    ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j)).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (NatTrans.app_homology (lim.π j) (shortComplexDiagram F)).symm

private theorem shortComplexHomologyLimit_compatibility
    (F : J ⥤ ShortComplex C) (j : J) :
    ((shortComplexDiagram F).mapHomologyIso lim).inv ≫
        ShortComplex.homologyMap
          ((shortComplexDiagram F).mapNatTrans (lim.π j) ≫
            (shortComplexDiagramEvaluationIso F j).hom) =
      (limit.π (shortComplexDiagram F).homology j ≫
          ((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j)).inv) ≫
        ShortComplex.homologyMap (shortComplexDiagramEvaluationIso F j).hom := by
  rw [ShortComplex.homologyMap_comp, ← Category.assoc, shortComplex_mapHomologyIso_limit]

/-- Homology of the limit cone `shortComplexLimCone F` is the chosen limit of the pointwise
homology diagram of `F`. -/
private noncomputable def shortComplexHomologyLimitConeIso (F : J ⥤ ShortComplex C) :
    (Cone.postcompose (shortComplexHomologyDiagramIso F).inv).obj
        (limit.cone (shortComplexDiagram F).homology) ≅
      (ShortComplex.homologyFunctor C).mapCone (shortComplexLimCone F) := by
  refine Cone.ext ((shortComplexDiagram F).mapHomologyIso lim).symm (fun j ↦ ?_)
  change limit.π (shortComplexDiagram F).homology j ≫
      (((shortComplexDiagram F).mapHomologyIso ((evaluation J C).obj j)).inv ≫
        ShortComplex.homologyMap (shortComplexDiagramEvaluationIso F j).hom) =
    ((shortComplexDiagram F).mapHomologyIso lim).inv ≫
      ShortComplex.homologyMap ((ShortComplex.limitCone F).π.app j)
  rw [← Category.assoc, ← shortComplexHomologyLimit_compatibility]
  congr 2
  ext <;>
    change _ ≫ 𝟙 _ = _ <;>
    simp <;>
    dsimp [shortComplexDiagram, ShortComplex.limitCone, ShortComplex.functorEquivalence,
      ShortComplex.FunctorEquivalence.inverse]

/-- Homology of short complexes preserves limits of any exact shape. -/
instance shortComplexHomologyFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J (ShortComplex.homologyFunctor C) where
  preservesLimit {F} :=
    preservesLimit_of_preserves_limit_cone
      (isLimitShortComplexLimCone F)
      ((IsLimit.equivOfNatIsoOfIso
        (shortComplexHomologyDiagramIso F).symm
        (limit.cone (shortComplexDiagram F).homology)
        ((ShortComplex.homologyFunctor C).mapCone (shortComplexLimCone F))
        (shortComplexHomologyLimitConeIso F)) (limit.isLimit _))

variable {I D : Type*} [Category D] [HasZeroMorphisms D] [HasLimitsOfShape J D]
  (c : ComplexShape I) (q : I)

/-- Sending a homological complex to its short complex at one degree preserves all existing
limits. -/
instance homologicalComplexShortComplexFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J
      (HomologicalComplex.shortComplexFunctor D c q) where
  preservesLimit {F} := by
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    apply ShortComplex.isLimitOfIsLimitπ
    · exact isLimitOfPreserves (HomologicalComplex.eval D c (c.prev q))
        (limit.isLimit F)
    · exact isLimitOfPreserves (HomologicalComplex.eval D c q)
        (limit.isLimit F)
    · exact isLimitOfPreserves (HomologicalComplex.eval D c (c.next q))
        (limit.isLimit F)

/-- Homology in any degree of a homological complex preserves limits of any exact shape. -/
instance homologicalComplexHomologyFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J
      (HomologicalComplex.homologyFunctor C c q) := by
  exact preservesLimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso C c q).symm

end TauCeti
