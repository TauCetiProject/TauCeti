/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Cech.Diagram
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.CoverGeneration

/-!
# Uniqueness for the fundamental-groupoid Čech cocone

For an open cover, a functor out of the ambient fundamental groupoid is determined by its
restrictions to the finite intersections in the Čech diagram. In fact the singleton intersections
suffice: subdivision of paths shows that the cover members generate every path class. This is
the uniqueness part of the colimit universal property of the Čech cocone.

The path-generation argument is the groupoid form of Brown, *Topology and Groupoids*,
Section 6.7.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped FundamentalGroupoid

universe u v

namespace TauCeti.FundamentalGroupoid

open TauCeti.TopCat

variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)

/-- Functors out of the ambient fundamental groupoid of an open cover are determined by their
composites with the singleton legs of the Čech cocone. -/
theorem cechCocone_hom_ext_singleton (hU : IsOpenCover U) {G : Grpd}
    {F H : (cechCocone U).pt ⟶ G}
    (h : ∀ i, (cechCocone U).ι.app (CechIndex.singleton i) ≫ F =
      (cechCocone U).ι.app (CechIndex.singleton i) ≫ H) : F = H := by
  apply TauCeti.FundamentalGroupoid.functor_ext
    (U := fun i ↦ (U i : Set X)) (fun x ↦ hU.exists_mem_nhds x)
  intro i
  let s := CechIndex.singleton i
  have hinc : eqToHom (cechTopDiagram_obj U s).symm ≫ cechInclusion U s =
      (TopCat.ofHom (ContinuousMap.subtypeVal (cechIntersection U s : Set X)) :
        TopCat.of (cechIntersection U s) ⟶ X) := by
    ext x
    exact cechInclusion_apply U s x
  have hpt : eqToHom (cechCocone_pt U) = 𝟙 ((cechCocone U).pt) := by rfl
  have hleg : _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
      (TopCat.ofHom (ContinuousMap.subtypeVal (cechIntersection U s : Set X))) =
      eqToHom (cechDiagram_obj U s).symm ≫ (cechCocone U).ι.app s := by
    have hcech := cechCocone_ι_app U s
    calc
      _ = eqToHom (cechDiagram_obj U s).symm ≫ (cechCocone U).ι.app s ≫
          eqToHom (cechCocone_pt U) := by
        simpa only [← Functor.map_comp, hinc] using hcech.symm
      _ = _ := by
        rw [hpt]
        exact (Category.assoc _ _ _).symm.trans (Category.comp_id _)
  have hi := congrArg (fun f => eqToHom (cechDiagram_obj U s).symm ≫ f) (h i)
  rw [← Category.assoc, ← hleg, ← Category.assoc, ← hleg] at hi
  dsimp only [s] at hi
  rw [cechIntersection_singleton] at hi
  exact hi

/-- Functors out of the ambient fundamental groupoid of an open cover are determined by their
composites with all the legs of the Čech cocone. -/
theorem cechCocone_hom_ext (hU : IsOpenCover U) {G : Grpd}
    {F H : (cechCocone U).pt ⟶ G}
    (h : ∀ s, (cechCocone U).ι.app s ≫ F = (cechCocone U).ι.app s ≫ H) : F = H :=
  cechCocone_hom_ext_singleton U hU (fun i ↦ h (CechIndex.singleton i))

end TauCeti.FundamentalGroupoid
