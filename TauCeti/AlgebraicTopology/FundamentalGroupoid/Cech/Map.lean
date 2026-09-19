/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Cech.Diagram
public import TauCeti.Topology.Category.TopCat.Cech.Map

/-!
# Maps of fundamental-groupoid Čech diagrams

A map of covered spaces induces a natural transformation between the corresponding
fundamental-groupoid Čech diagrams.  Its components commute with the canonical cocones into the
ambient fundamental groupoids.  Thus a natural map on the eventual Čech colimits is forced to be
the usual map on fundamental groupoids.

## References

* R. Brown, *Topology and Groupoids*, Chapters 6--7.
* T. Zhu, [mathlib4#41603](https://github.com/leanprover-community/mathlib4/pull/41603), whose
  fundamental-groupoid cosheaf interface guides the colimit formulation.
-/

public section

noncomputable section

open CategoryTheory Limits Set TopologicalSpace
open scoped FundamentalGroupoid

universe u v z

namespace TauCeti.FundamentalGroupoid

open TauCeti.TopCat

variable {X Y : TopCat.{v}} {ι : Type u} {κ : Type z}
  (U : ι → Opens X) (V : κ → Opens Y) (f : X ⟶ Y) (r : ι → κ)
  (hf : ∀ i, MapsTo f (U i) (V (r i)))

include hf

/-- A map of covered spaces induces a natural transformation between the corresponding
fundamental-groupoid Čech diagrams. -/
def cechMapNatTrans :
    cechDiagram U ⟶ CechIndex.map r ⋙ cechDiagram V :=
  Functor.whiskerRight (TopCat.cechMapNatTrans U V f r hf)
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor

@[simp]
lemma cechMapNatTrans_app (s : CechIndex ι) :
    (cechMapNatTrans U V f r hf).app s =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        (TopCat.cechMap U V f r hf s) := by
  rw [cechMapNatTrans, Functor.whiskerRight_app, TopCat.cechMapNatTrans_app]

/-- The natural transformation induced by a map of covered spaces commutes with the canonical
cocones into the ambient fundamental groupoids. -/
@[reassoc]
lemma cechMap_comp_cocone (s : CechIndex ι) :
    (cechMapNatTrans U V f r hf).app s ≫
        (cechCocone V).ι.app ((CechIndex.map r).obj s) =
      (cechCocone U).ι.app s ≫
        _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map f := by
  rw [cechMapNatTrans_app]
  simp only [cechCocone, Functor.mapCocone_ι_app, TopCat.cechInclusionNatTrans_app]
  simpa only [cechDiagram, cechCocone, Functor.mapCocone_pt, Functor.map_comp] using congrArg
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
      (TopCat.cechMap_comp_inclusion U V f r hf s)

/-- The target Čech cocone, restricted along a map of covered spaces, as a cocone on the
source Čech diagram. -/
@[expose]
def cechMapCocone : Cocone (cechDiagram U) :=
  (Cocone.precompose (cechMapNatTrans U V f r hf)).obj
    ((cechCocone V).whisker (CechIndex.map r))

@[simp]
lemma cechMapCocone_pt : (cechMapCocone U V f r hf).pt = (cechCocone V).pt := by
  simp only [cechMapCocone, Cocone.precompose_obj_pt, Cocone.whisker_pt]

@[simp]
lemma cechMapCocone_ι_app (s : CechIndex ι) :
    (cechMapCocone U V f r hf).ι.app s =
      (cechMapNatTrans U V f r hf).app s ≫
        (cechCocone V).ι.app ((CechIndex.map r).obj s) := by
  simp only [cechMapCocone, Cocone.precompose_obj_ι, Cocone.whisker_ι, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.const_obj_obj, Functor.comp_obj]

/-- If the source canonical cocone is colimiting, then its induced map to the target canonical
cocone is the usual map on fundamental groupoids.  This is the map-level naturality statement
needed by the Čech colimit form of van Kampen. -/
lemma isColimit_desc_cechMapCocone (hU : IsColimit (cechCocone U)) :
    hU.desc (cechMapCocone U V f r hf) =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map f := by
  apply hU.hom_ext
  intro s
  rw [hU.fac]
  exact cechMap_comp_cocone U V f r hf s

end TauCeti.FundamentalGroupoid
