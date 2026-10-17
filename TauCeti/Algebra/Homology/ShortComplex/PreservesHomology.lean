/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology classes and diagrams under functors preserving homology

For a functor `F` preserving the left homology of a short complex `S`, Mathlib identifies the
cycles and the homology of `S.map F` with the images under `F` of those of `S`, by
`ShortComplex.mapCyclesIso` and `ShortComplex.mapHomologyIso`, and records how the first of them
interacts with the inclusion of the cycles (`ShortComplex.mapCyclesIso_hom_iCycles`). This file
records the companion statement for the class map: under the two identifications, the class map
`homologyπ` of `S.map F` is the image under `F` of the class map of `S`
(`ShortComplex.homologyπ_comp_mapHomologyIso_hom`).

It also provides the natural isomorphism `ShortComplex.homologyDiagramIso` identifying the
pointwise homology diagram `F ⋙ ShortComplex.homologyFunctor C` of a diagram
`F : J ⥤ ShortComplex C` with the homology of the associated short complex of diagrams
`(functorEquivalence J C).inverse.obj F` whenever evaluation at each object preserves homology.
-/

public section

namespace CategoryTheory.ShortComplex

section Map

variable {C D : Type*} [Category C] [Category D] [Limits.HasZeroMorphisms C]
  [Limits.HasZeroMorphisms D] (S : ShortComplex C) (F : C ⥤ D) [F.PreservesZeroMorphisms]

/-- The inverse cycles identification carries the inclusion of cycles in the mapped complex to
the image of the original inclusion. -/
@[reassoc (attr := simp)]
theorem mapCyclesIso_inv_comp_iCycles [S.HasLeftHomology] [F.PreservesLeftHomologyOf S] :
    (S.mapCyclesIso F).inv ≫ (S.map F).iCycles = F.map S.iCycles := by
  rw [Iso.inv_comp_eq, mapCyclesIso_hom_iCycles]

/-- **The class map commutes with a functor preserving homology.** Under the identifications
`mapCyclesIso` and `mapHomologyIso`, the class map of `S.map F` is the image under `F` of the
class map of `S`. -/
@[reassoc (attr := simp)]
theorem homologyπ_comp_mapHomologyIso_hom [S.HasHomology] [(S.map F).HasHomology]
    [F.PreservesLeftHomologyOf S] :
    (S.map F).homologyπ ≫ (S.mapHomologyIso F).hom =
      (S.mapCyclesIso F).hom ≫ F.map S.homologyπ := by
  -- Both identifications are computed from the left homology data `h` of `S`. The objects of
  -- `h.map F` are those of `h` under `F` only after unfolding, so rewriting with
  -- `LeftHomologyData.mapHomologyIso_eq` produces goals that are not type-correct at reducible
  -- transparency; the squares are therefore pasted as terms.
  let h := S.leftHomologyData
  exact (congrArg ((S.map F).homologyπ ≫ ·)
      (congrArg Iso.hom (LeftHomologyData.mapHomologyIso_eq h F))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ F.map h.homologyIso.inv) (h.map F).homologyπ_comp_homologyIso_hom).trans <|
    (Category.assoc _ _ _).trans <|
    (congrArg ((h.map F).cyclesIso.hom ≫ ·) ((F.map_comp _ _).symm.trans
      ((congrArg F.map h.π_comp_homologyIso_inv).trans (F.map_comp _ _)))).trans <|
    (Category.assoc _ _ _).symm.trans <|
    congrArg (· ≫ F.map S.homologyπ)
      (congrArg Iso.hom (LeftHomologyData.mapCyclesIso_eq h F)).symm

end Map

section Diagram

variable {C J : Type*} [Category* C] [Limits.HasZeroMorphisms C] [Category* J]

/-- Evaluating the short complex of diagrams attached to `F : J ⥤ ShortComplex C` at `j` gives
back `F.obj j`. This is the component at `j` of the counit of `ShortComplex.functorEquivalence`,
stated with the evaluated short complex as its source so that later composites are well typed.
The definition is `@[expose]`d so that its object components are definitionally identities in
downstream modules. -/
@[expose]
def diagramEvaluationIso (F : J ⥤ ShortComplex C) (j : J) :
    ((functorEquivalence J C).inverse.obj F).map ((evaluation J C).obj j) ≅ F.obj j :=
  ((functorEquivalence J C).counitIso.app F).app j

/-- Naturality of the forward morphism of `ShortComplex.diagramEvaluationIso`. -/
@[reassoc]
theorem diagramEvaluationIso_hom_naturality (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    ((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f) ≫
        (diagramEvaluationIso F Y).hom =
      (diagramEvaluationIso F X).hom ≫ F.map f :=
  ((functorEquivalence J C).counitIso.app F).hom.naturality f

/-- Naturality of the inverse morphism of `ShortComplex.diagramEvaluationIso`. -/
@[reassoc]
theorem diagramEvaluationIso_inv_naturality (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    F.map f ≫ (diagramEvaluationIso F Y).inv =
      (diagramEvaluationIso F X).inv ≫
        ((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f) := by
  rw [Iso.comp_inv_eq, Category.assoc, diagramEvaluationIso_hom_naturality, Iso.inv_hom_id_assoc]

variable [CategoryWithHomology C] [CategoryWithHomology (J ⥤ C)]

/-- The pointwise homology diagram of `F : J ⥤ ShortComplex C` is naturally isomorphic to the
homology of the associated short complex of diagrams when evaluation at each object preserves
homology. -/
@[expose]
noncomputable def homologyDiagramIso (F : J ⥤ ShortComplex C)
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] :
    F ⋙ homologyFunctor C ≅ ((functorEquivalence J C).inverse.obj F).homology :=
  NatIso.ofComponents
    (fun j ↦ homologyMapIso (diagramEvaluationIso F j).symm ≪≫
      ((functorEquivalence J C).inverse.obj F).mapHomologyIso ((evaluation J C).obj j))
    (fun {X Y} f ↦ by
      have h_eval :
          homologyMap
              (((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f)) ≫
            (((functorEquivalence J C).inverse.obj F).mapHomologyIso
              ((evaluation J C).obj Y)).hom =
          (((functorEquivalence J C).inverse.obj F).mapHomologyIso
              ((evaluation J C).obj X)).hom ≫
            ((functorEquivalence J C).inverse.obj F).homology.map f := by
        rw [← Iso.inv_comp_eq]
        exact (NatTrans.app_homology ((evaluation J C).map f)
          ((functorEquivalence J C).inverse.obj F)).symm
      have h : homologyMap (F.map f) ≫
            (homologyMap (diagramEvaluationIso F Y).inv ≫
              (((functorEquivalence J C).inverse.obj F).mapHomologyIso
                ((evaluation J C).obj Y)).hom) =
          (homologyMap (diagramEvaluationIso F X).inv ≫
              (((functorEquivalence J C).inverse.obj F).mapHomologyIso
                ((evaluation J C).obj X)).hom) ≫
            ((functorEquivalence J C).inverse.obj F).homology.map f := by
        rw [Category.assoc, ← h_eval, ← Category.assoc,
          ← Category.assoc, ← homologyMap_comp, ← homologyMap_comp,
          diagramEvaluationIso_inv_naturality]
      exact h)

/-- The forward component of `ShortComplex.homologyDiagramIso` at `j`. -/
@[simp]
theorem homologyDiagramIso_hom_app (F : J ⥤ ShortComplex C)
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] (j : J) :
    (homologyDiagramIso F).hom.app j =
      homologyMap (diagramEvaluationIso F j).inv ≫
        (((functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).hom :=
  (rfl)

/-- The inverse component of `ShortComplex.homologyDiagramIso` at `j`. -/
@[simp]
theorem homologyDiagramIso_inv_app (F : J ⥤ ShortComplex C)
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] (j : J) :
    (homologyDiagramIso F).inv.app j =
      (((functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).inv ≫
        homologyMap (diagramEvaluationIso F j).hom :=
  (rfl)

end Diagram

end CategoryTheory.ShortComplex
