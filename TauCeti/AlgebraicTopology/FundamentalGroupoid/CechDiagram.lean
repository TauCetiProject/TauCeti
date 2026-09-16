/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import TauCeti.Topology.Category.TopCat.CechDiagram

/-!
# The fundamental-groupoid Čech diagram of a family of open sets

For a family `U : ι → Opens X`, this file maps its topological Čech diagram through the
fundamental-groupoid functor and constructs the canonical cocone to the fundamental groupoid of
`X`. The cocone is the input for the groupoid van Kampen colimit theorem.

## References

* R. Brown, *Topology and Groupoids*, Chapters 6--7.
* T. Zhu, [mathlib4#41603](https://github.com/leanprover-community/mathlib4/pull/41603), whose
  open-set and fundamental-groupoid object and map shapes guide this interface.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped FundamentalGroupoid

universe u v

namespace TauCeti.FundamentalGroupoid

open TauCeti.TopCat

variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)

/-- The fundamental-groupoid Čech diagram of a family of open sets. -/
def cechDiagram : CechIndex ι ⥤ Grpd :=
  cechTopDiagram U ⋙ _root_.FundamentalGroupoid.fundamentalGroupoidFunctor

@[simp]
lemma cechDiagram_obj (s : CechIndex ι) :
    (cechDiagram U).obj s =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj
        (TopCat.of (cechIntersection U s)) := by
  rw [cechDiagram, Functor.comp_obj, cechTopDiagram_obj]

@[simp]
lemma cechDiagram_map {s t : CechIndex ι} (f : s ⟶ t) :
    eqToHom (cechDiagram_obj U s).symm ≫ (cechDiagram U).map f ≫
        eqToHom (cechDiagram_obj U t) =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        (eqToHom (cechTopDiagram_obj U s).symm ≫ (cechTopDiagram U).map f ≫
          eqToHom (cechTopDiagram_obj U t)) := by
  unfold cechDiagram
  simp only [Functor.comp_map, Functor.map_comp, eqToHom_map]

private def cechDiagramIso :
    cechDiagram U ≅
      cechTopDiagram U ⋙ _root_.FundamentalGroupoid.fundamentalGroupoidFunctor :=
  eqToIso (by unfold cechDiagram; rfl)

/-- The canonical cocone from the Čech diagram to the fundamental groupoid of the ambient space. -/
def cechCocone : Cocone (cechDiagram U) :=
  (Cocone.precompose (cechDiagramIso U).hom).obj
    (_root_.FundamentalGroupoid.fundamentalGroupoidFunctor.mapCocone
      (Cocone.mk X (cechInclusionNatTrans U)))

@[simp]
lemma cechCocone_pt : (cechCocone U).pt =
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj X := by
  rfl

@[simp]
lemma cechCocone_ι_app (s : CechIndex ι) :
    eqToHom (cechDiagram_obj U s).symm ≫ (cechCocone U).ι.app s ≫
        eqToHom (cechCocone_pt U) =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        (eqToHom (cechTopDiagram_obj U s).symm ≫ cechInclusion U s) := by
  simp only [cechCocone, Cocone.precompose_obj_ι, NatTrans.comp_app,
    Functor.mapCocone_ι_app, cechInclusionNatTrans_app, Functor.map_comp, eqToHom_map]
  rfl

end TauCeti.FundamentalGroupoid
