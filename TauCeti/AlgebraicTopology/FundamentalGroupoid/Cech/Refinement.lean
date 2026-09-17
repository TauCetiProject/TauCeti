/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Cech.Diagram
public import TauCeti.Topology.Category.TopCat.Cech.Refinement

/-!
# Refinements of fundamental-groupoid Čech diagrams

A chosen refinement `r` from a family of open sets `U` to a family `V`, with
`U i ⊆ V (r i)`, sends every finite intersection for `U` into the intersection for the image of
its indices under `r`. Applying the fundamental-groupoid functor to these inclusions gives a
natural transformation between the corresponding Čech diagrams.

The transformation commutes with the legs of the canonical cocones into the fundamental groupoid
of the ambient space.

## References

* R. Brown, *Topology and Groupoids*, Chapters 6--7.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace
open scoped FundamentalGroupoid

universe u v w

namespace TauCeti.FundamentalGroupoid

open TauCeti.TopCat

variable {X : TopCat.{w}} {ι : Type u} {κ : Type v} (U : ι → Opens X) (V : κ → Opens X)
  (r : ι → κ) (hr : ∀ i, U i ≤ V (r i))

include hr

/-- A chosen refinement induces a natural transformation between the fundamental-groupoid Čech
diagrams. -/
def cechRefinementNatTrans :
    cechDiagram U ⟶ CechIndex.map r ⋙ cechDiagram V :=
  Functor.whiskerRight (TopCat.cechRefinementNatTrans U V r hr)
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor

@[simp]
lemma cechRefinementNatTrans_app (s : CechIndex ι) :
    (cechRefinementNatTrans U V r hr).app s =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        (TopCat.cechRefinement U V r hr s) := by
  rw [cechRefinementNatTrans, Functor.whiskerRight_app, TopCat.cechRefinementNatTrans_app]

/-- The natural transformation induced by a refinement commutes with the canonical cocones into
the ambient fundamental groupoid. -/
@[reassoc]
lemma cechRefinement_comp_cocone (s : CechIndex ι) :
    (cechRefinementNatTrans U V r hr).app s ≫
        (cechCocone V).ι.app ((CechIndex.map r).obj s) =
      (cechCocone U).ι.app s := by
  rw [cechRefinementNatTrans_app]
  simp only [cechCocone, Functor.mapCocone_ι_app, TopCat.cechInclusionNatTrans_app]
  simpa only [cechDiagram, cechCocone, Functor.mapCocone_pt, Functor.map_comp] using congrArg
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
      (TopCat.cechRefinement_comp_inclusion U V r hr s)

end TauCeti.FundamentalGroupoid
