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

The section is `@[expose]` for the same reason as the topological Čech diagram: the groupoid
diagram and its cocone stay definitionally the images of that diagram and of its inclusions.

The finite-intersection presentation follows R. Brown, *Topology and Groupoids*, Chapters 6--7.
-/

@[expose] public section

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
        (TopCat.of (cechIntersection U s)) :=
  rfl

@[simp]
lemma cechDiagram_map {s t : CechIndex ι} (f : s ⟶ t) :
    (cechDiagram U).map f =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map ((cechTopDiagram U).map f) :=
  rfl

/-- The canonical cocone from the Čech diagram to the fundamental groupoid of the ambient space. -/
def cechCocone : Cocone (cechDiagram U) :=
  _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.mapCocone
    (Cocone.mk X (cechInclusionNatTrans U))

@[simp]
lemma cechCocone_pt : (cechCocone U).pt =
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj X :=
  rfl

@[simp]
lemma cechCocone_ι_app (s : CechIndex ι) :
    (cechCocone U).ι.app s =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map (cechInclusion U s) :=
  rfl

end TauCeti.FundamentalGroupoid
