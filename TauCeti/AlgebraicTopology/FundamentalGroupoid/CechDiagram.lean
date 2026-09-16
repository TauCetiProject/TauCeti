/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sets.OpenCover

/-!
# The Čech diagram of an open cover

For a family `U : ι → Opens X`, the Čech index category consists of the nonempty finite subsets
of `ι`, ordered by reverse inclusion.  An index `s` represents the intersection `⋂ i ∈ s, U i`;
reverse inclusion makes the evident inclusions of intersections into morphisms in `Opens X`.

This file constructs the resulting diagrams in open sets, topological spaces, and groupoids, and
the canonical cocone from the groupoid diagram to the fundamental groupoid of `X`.  The cocone is
the input for the groupoid van Kampen colimit theorem.

The finite-intersection presentation follows R. Brown, *Topology and Groupoids*, Chapters 6--7.
The object and map shapes agree with the open-set formulation of
[mathlib4#41603](https://github.com/leanprover-community/mathlib4/pull/41603); no code from that
pull request is used here.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped FundamentalGroupoid

universe u v

namespace TauCeti.FundamentalGroupoid

/-- The indices for the Čech diagram of a cover: nonempty finite sets of cover members, ordered
by reverse inclusion. -/
abbrev CechIndex (ι : Type u) := OrderDual {s : Finset ι // s.Nonempty}

namespace CechIndex

variable {ι : Type u}

/-- The Čech index consisting of one cover member. -/
def singleton (i : ι) : CechIndex ι :=
  OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩

@[simp]
lemma coe_singleton (i : ι) : (singleton i).1 = {i} := (rfl)

/-- The order on Čech indices is reverse inclusion of the underlying finite sets. -/
@[simp]
lemma le_iff {s t : CechIndex ι} : s ≤ t ↔ t.1 ⊆ s.1 := Iff.rfl

end CechIndex

variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)

/-- The open set represented by a Čech index: the intersection of its cover members. -/
def cechIntersection (s : CechIndex ι) : Opens X :=
  s.1.inf U

@[simp]
lemma cechIntersection_singleton (i : ι) :
    cechIntersection U (CechIndex.singleton i) = U i := by
  change ({i} : Finset ι).inf U = U i
  exact Finset.inf_singleton

/-- Enlarging the finite set of cover members shrinks its intersection. -/
lemma cechIntersection_mono {s t : CechIndex ι} (h : s ≤ t) :
    cechIntersection U s ≤ cechIntersection U t := by
  refine Finset.le_inf fun i hi ↦ ?_
  exact Finset.inf_le (f := U) (h hi)

/-- The diagram of nonempty finite intersections of a family of open sets. -/
def cechOpenDiagram : CechIndex ι ⥤ Opens X where
  obj := cechIntersection U
  map f := homOfLE (cechIntersection_mono U f.le)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

@[simp]
lemma cechOpenDiagram_obj (s : CechIndex ι) :
    (cechOpenDiagram U).obj s = cechIntersection U s := rfl

@[simp]
lemma cechOpenDiagram_map {s t : CechIndex ι} (f : s ⟶ t) :
    (cechOpenDiagram U).map f = homOfLE (cechIntersection_mono U f.le) := rfl

/-- The topological-space Čech diagram of an open cover. -/
def cechTopDiagram : CechIndex ι ⥤ TopCat :=
  cechOpenDiagram U ⋙ Opens.toTopCat X

@[simp]
lemma cechTopDiagram_obj (s : CechIndex ι) :
    (cechTopDiagram U).obj s = TopCat.of (cechIntersection U s) := rfl

@[simp]
lemma cechTopDiagram_map_apply {s t : CechIndex ι} (f : s ⟶ t)
    (x : (cechTopDiagram U).obj s) :
    (cechTopDiagram U).map f x =
      ⟨x.1, cechIntersection_mono U f.le x.2⟩ := rfl

/-- The inclusion of a finite cover intersection into the ambient space. -/
def cechInclusion (s : CechIndex ι) : (cechTopDiagram U).obj s ⟶ X :=
  Opens.inclusion' (cechIntersection U s)

@[simp]
lemma cechInclusion_apply (s : CechIndex ι) (x : (cechTopDiagram U).obj s) :
    cechInclusion U s x = x.1 := rfl

@[reassoc]
lemma cechTopDiagram_map_comp_inclusion {s t : CechIndex ι} (f : s ⟶ t) :
    (cechTopDiagram U).map f ≫ cechInclusion U t = cechInclusion U s := by
  ext x
  rfl

/-- The inclusions of finite intersections into the ambient space form a natural transformation. -/
def cechInclusionNatTrans :
    cechTopDiagram U ⟶ (Functor.const (CechIndex ι)).obj X where
  app := cechInclusion U
  naturality _ _ f := cechTopDiagram_map_comp_inclusion U f

@[simp]
lemma cechInclusionNatTrans_app (s : CechIndex ι) :
    (cechInclusionNatTrans U).app s = cechInclusion U s := rfl

/-- The fundamental-groupoid Čech diagram of an open cover. -/
def cechDiagram : CechIndex ι ⥤ Grpd :=
  cechTopDiagram U ⋙ _root_.FundamentalGroupoid.fundamentalGroupoidFunctor

@[simp]
lemma cechDiagram_obj (s : CechIndex ι) :
    (cechDiagram U).obj s =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj
        (TopCat.of (cechIntersection U s)) := rfl

@[simp]
lemma cechDiagram_map {s t : CechIndex ι} (f : s ⟶ t) :
    (cechDiagram U).map f =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        ((cechTopDiagram U).map f) := rfl

/-- The canonical cocone from the Čech diagram to the fundamental groupoid of the ambient space. -/
def cechCocone : Cocone (cechDiagram U) where
  pt := _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj X
  ι.app s := _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map (cechInclusion U s)
  ι.naturality s t f := by
    change _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map
        ((cechTopDiagram U).map f) ≫
          _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map (cechInclusion U t) =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map (cechInclusion U s)
    rw [← Functor.map_comp, cechTopDiagram_map_comp_inclusion]

@[simp]
lemma cechCocone_pt : (cechCocone U).pt =
    _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.obj X := rfl

@[simp]
lemma cechCocone_ι_app (s : CechIndex ι) :
    (cechCocone U).ι.app s =
      _root_.FundamentalGroupoid.fundamentalGroupoidFunctor.map (cechInclusion U s) := rfl

/-- Every point of an open cover occurs already in a singleton object of its Čech diagram. -/
lemma exists_mem_cechIntersection_singleton (hU : IsOpenCover U) (x : X) :
    ∃ i, x ∈ cechIntersection U (CechIndex.singleton i) := by
  simpa using hU.exists_mem x

end TauCeti.FundamentalGroupoid
