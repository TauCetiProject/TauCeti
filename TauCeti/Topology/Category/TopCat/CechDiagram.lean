/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sets.OpenCover

/-!
# The Čech diagram of a family of open sets

For a family `U : ι → Opens X`, the Čech index category consists of the nonempty finite subsets
of `ι`, ordered by reverse inclusion. An index `s` represents the intersection `⋂ i ∈ s, U i`;
reverse inclusion makes the evident inclusions of intersections into morphisms in `Opens X`.

This file constructs the resulting diagrams in open sets and topological spaces, together with
the natural transformation formed by the inclusions of the finite intersections into `X`.

The finite-intersection presentation follows R. Brown, *Topology and Groupoids*, Chapters 6--7.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u v

namespace TauCeti.TopCat

/-- The indices for the Čech diagram of a family of open sets: nonempty finite subsets of the
indexing type, ordered by reverse inclusion. -/
abbrev CechIndex (ι : Type u) := OrderDual {s : Finset ι // s.Nonempty}

namespace CechIndex

variable {ι : Type u}

/-- The Čech index consisting of one family member. -/
def singleton (i : ι) : CechIndex ι :=
  OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩

@[simp]
lemma coe_singleton (i : ι) : (singleton i).1 = {i} := (rfl)

/-- The order on Čech indices is reverse inclusion of the underlying finite sets. -/
@[simp]
lemma le_iff {s t : CechIndex ι} : s ≤ t ↔ t.1 ⊆ s.1 := Iff.rfl

end CechIndex

variable {X : TopCat.{v}} {ι : Type u} (U : ι → Opens X)

/-- The open set represented by a Čech index: the intersection of its family members. -/
def cechIntersection (s : CechIndex ι) : Opens X :=
  s.1.inf U

@[simp]
lemma cechIntersection_singleton (i : ι) :
    cechIntersection U (CechIndex.singleton i) = U i := by
  unfold cechIntersection CechIndex.singleton
  exact Finset.inf_singleton

/-- Enlarging the finite set of family members shrinks its intersection. -/
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
    (cechOpenDiagram U).obj s = cechIntersection U s := (rfl)

@[simp]
lemma cechOpenDiagram_map {s t : CechIndex ι} (f : s ⟶ t) :
    (cechOpenDiagram U).map f =
      eqToHom (cechOpenDiagram_obj U s) ≫ homOfLE (cechIntersection_mono U f.le) ≫
        eqToHom (cechOpenDiagram_obj U t).symm :=
  Subsingleton.elim _ _

/-- The topological-space Čech diagram of a family of open sets. -/
def cechTopDiagram : CechIndex ι ⥤ TopCat :=
  cechOpenDiagram U ⋙ Opens.toTopCat X

@[simp]
lemma cechTopDiagram_obj (s : CechIndex ι) :
    (cechTopDiagram U).obj s = TopCat.of (cechIntersection U s) := (rfl)

@[simp]
lemma cechTopDiagram_map_apply {s t : CechIndex ι} (f : s ⟶ t)
    (x : TopCat.of (cechIntersection U s)) :
    ConcreteCategory.hom
      (eqToHom (cechTopDiagram_obj U s).symm ≫ (cechTopDiagram U).map f ≫
        eqToHom (cechTopDiagram_obj U t)) x =
      ⟨x.1, cechIntersection_mono U f.le x.2⟩ := by
  unfold cechTopDiagram cechOpenDiagram cechIntersection
  rfl

/-- The inclusion of a finite-family intersection into the ambient space. -/
def cechInclusion (s : CechIndex ι) : (cechTopDiagram U).obj s ⟶ X :=
  Opens.inclusion' (cechIntersection U s)

@[simp]
lemma cechInclusion_apply (s : CechIndex ι) (x : TopCat.of (cechIntersection U s)) :
    ConcreteCategory.hom
      (eqToHom (cechTopDiagram_obj U s).symm ≫ cechInclusion U s) x = x.1 := by
  unfold cechInclusion cechTopDiagram cechOpenDiagram cechIntersection
  rfl

@[reassoc]
lemma cechTopDiagram_map_comp_inclusion {s t : CechIndex ι} (f : s ⟶ t) :
    (cechTopDiagram U).map f ≫ cechInclusion U t = cechInclusion U s := by
  ext x
  rfl

/-- The inclusions of finite-family intersections into the ambient space form a natural
transformation. -/
def cechInclusionNatTrans :
    cechTopDiagram U ⟶ (Functor.const (CechIndex ι)).obj X where
  app := cechInclusion U
  naturality _ _ f := cechTopDiagram_map_comp_inclusion U f

@[simp]
lemma cechInclusionNatTrans_app (s : CechIndex ι) :
    (cechInclusionNatTrans U).app s = cechInclusion U s := (rfl)

/-- Every point of an open cover occurs already in a singleton object of its Čech diagram. -/
lemma exists_mem_cechIntersection_singleton (hU : IsOpenCover U) (x : X) :
    ∃ i, x ∈ cechIntersection U (CechIndex.singleton i) := by
  simpa using hU.exists_mem x

end TauCeti.TopCat
