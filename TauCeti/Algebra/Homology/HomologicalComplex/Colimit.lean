/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Diagrams and cocones of functors applied to homological complexes

Given a diagram `G : T ⥤ C ⥤ D` of zero-preserving functors and a homological complex
`K : HomologicalComplex C c`, applying `G` termwise yields a diagram `K.mapDiagram G` in
`HomologicalComplex D c`. Any cocone `s` on `G` whose point preserves zero morphisms yields a
cocone `K.mapCocone s` on `K.mapDiagram G`, and if `s` is colimiting and evaluation at each
degree `K.X m` preserves colimits of `G`, then `K.mapCocone s` is colimiting
(`HomologicalComplex.isColimitMapCocone`).

## Main definitions

* `HomologicalComplex.mapDiagram`: applies a diagram `G : T ⥤ C ⥤ D` termwise to `K`.
* `HomologicalComplex.mapCocone`: applies a cocone `s` on `G` termwise to `K`.
* `HomologicalComplex.isColimitMapCocone`: `K.mapCocone s` is a colimit cocone whenever `s` is
  and evaluation at each `K.X m` preserves colimits of `G`.
-/

public section

open CategoryTheory Limits

namespace HomologicalComplex

variable {T : Type*} [Category* T] {C D : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] {ι : Type*} {c : ComplexShape ι}

/-- Applying a diagram `G : T ⥤ C ⥤ D` of zero-preserving functors termwise to a homological
complex `K` yields a diagram `T ⥤ HomologicalComplex D c`. -/
@[simps]
noncomputable abbrev mapDiagram (K : HomologicalComplex C c) (G : T ⥤ C ⥤ D)
    [∀ t, (G.obj t).PreservesZeroMorphisms] : T ⥤ HomologicalComplex D c where
  obj t := ((G.obj t).mapHomologicalComplex c).obj K
  map w := (NatTrans.mapHomologicalComplex (G.map w) c).app K
  map_id t := by simp
  map_comp f g := by simp

/-- Applying a cocone `s` on `G : T ⥤ C ⥤ D` termwise to a homological complex `K` yields a
cocone on `K.mapDiagram G`. -/
@[simps]
noncomputable abbrev mapCocone (K : HomologicalComplex C c) {G : T ⥤ C ⥤ D}
    [∀ t, (G.obj t).PreservesZeroMorphisms] (s : Cocone G) [s.pt.PreservesZeroMorphisms] :
    Cocone (K.mapDiagram G) where
  pt := (s.pt.mapHomologicalComplex c).obj K
  ι :=
    { app t := (NatTrans.mapHomologicalComplex (F := G.obj t) (G := s.pt) (s.ι.app t) c).app K
      -- each naturality square is `s.w` applied termwise to `K`
      naturality t₁ t₂ w := by
        dsimp only
        simp only [Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id,
          ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp, s.w w] }

/-- If `s` is a colimit cocone on `G : T ⥤ C ⥤ D` and evaluation at each `K.X m` preserves
colimits of `G`, then `K.mapCocone s` is a colimit cocone on `K.mapDiagram G`. -/
noncomputable def isColimitMapCocone (K : HomologicalComplex C c) {G : T ⥤ C ⥤ D}
    [∀ t, (G.obj t).PreservesZeroMorphisms] {s : Cocone G} [s.pt.PreservesZeroMorphisms]
    (hs : IsColimit s) [∀ m, PreservesColimit G ((evaluation C D).obj (K.X m))] :
    IsColimit (K.mapCocone s) :=
  HomologicalComplex.isColimitOfEval _ _ fun m ↦ IsColimit.ofIsoColimit
    (isColimitOfPreserves ((evaluation C D).obj (K.X m)) hs)
    (Cocone.ext (Iso.refl _) fun t ↦ by simp)

end HomologicalComplex
