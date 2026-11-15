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
  have hleg := map_subtypeVal_eq_cechCocone_ι_app U s
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
