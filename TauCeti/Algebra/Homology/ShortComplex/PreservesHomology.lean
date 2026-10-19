/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import TauCeti.Algebra.Homology.ShortComplex.FunctorEquivalence

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
`(functorEquivalence J C).inverse.obj F` when that short complex has homology
(`((functorEquivalence J C).inverse.obj F).HasHomology`) and evaluation at each object preserves
its left and right homology.
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

/-- Evaluating the homology of the short complex of diagrams attached to `F : J ⥤ ShortComplex C`
along a morphism `f : X ⟶ Y` commutes with `ShortComplex.mapHomologyIso`. -/
@[reassoc]
theorem mapHomologyIso_evaluation_naturality (F : J ⥤ ShortComplex C)
    [((functorEquivalence J C).inverse.obj F).HasHomology]
    {X Y : J} (f : X ⟶ Y)
    [((evaluation J C).obj X).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [((evaluation J C).obj X).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [((evaluation J C).obj Y).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [((evaluation J C).obj Y).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] :
    homologyMap
        (((functorEquivalence J C).inverse.obj F).mapNatTrans ((evaluation J C).map f)) ≫
      (((functorEquivalence J C).inverse.obj F).mapHomologyIso
        ((evaluation J C).obj Y)).hom =
    (((functorEquivalence J C).inverse.obj F).mapHomologyIso
        ((evaluation J C).obj X)).hom ≫
      ((functorEquivalence J C).inverse.obj F).homology.map f := by
  -- Since `((evaluation J C).map f).app G = G.map f`, the right-hand factor is the component of
  -- `NatTrans.app_homology ((evaluation J C).map f)` on `(functorEquivalence J C).inverse.obj F`.
  rw [← Iso.inv_comp_eq]
  exact (NatTrans.app_homology ((evaluation J C).map f)
    ((functorEquivalence J C).inverse.obj F)).symm

variable [CategoryWithHomology C]

/-- The pointwise homology diagram of `F : J ⥤ ShortComplex C` is naturally isomorphic to the
homology of the associated short complex of diagrams `(functorEquivalence J C).inverse.obj F` when
`((functorEquivalence J C).inverse.obj F).HasHomology` holds and evaluation at each object
preserves its left and right homology. -/
noncomputable def homologyDiagramIso (F : J ⥤ ShortComplex C)
    [((functorEquivalence J C).inverse.obj F).HasHomology]
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] :
    F ⋙ homologyFunctor C ≅ ((functorEquivalence J C).inverse.obj F).homology :=
  NatIso.ofComponents
    (fun j ↦ homologyMapIso (diagramEvaluationIso F j).symm ≪≫
      ((functorEquivalence J C).inverse.obj F).mapHomologyIso ((evaluation J C).obj j))
    (fun {X Y} f ↦ by
      dsimp [homologyFunctor, homologyMapIso]
      rw [Category.assoc, ← mapHomologyIso_evaluation_naturality F f, ← Category.assoc,
        ← Category.assoc, ← homologyMap_comp, ← homologyMap_comp,
        diagramEvaluationIso_inv_naturality])

/-- The forward component of `ShortComplex.homologyDiagramIso` at `j`. -/
@[simp]
theorem homologyDiagramIso_hom_app (F : J ⥤ ShortComplex C)
    [((functorEquivalence J C).inverse.obj F).HasHomology]
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] (j : J) :
    (homologyDiagramIso F).hom.app j =
      homologyMap (diagramEvaluationIso F j).inv ≫
        (((functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).hom := by rfl

/-- The inverse component of `ShortComplex.homologyDiagramIso` at `j`. -/
@[simp]
theorem homologyDiagramIso_inv_app (F : J ⥤ ShortComplex C)
    [((functorEquivalence J C).inverse.obj F).HasHomology]
    [∀ j : J, ((evaluation J C).obj j).PreservesLeftHomologyOf
      ((functorEquivalence J C).inverse.obj F)]
    [∀ j : J, ((evaluation J C).obj j).PreservesRightHomologyOf
      ((functorEquivalence J C).inverse.obj F)] (j : J) :
    (homologyDiagramIso F).inv.app j =
      (((functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).inv ≫
        homologyMap (diagramEvaluationIso F j).hom := by rfl

end Diagram

end CategoryTheory.ShortComplex
