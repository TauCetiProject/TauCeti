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
the natural transformation formed by the inclusions of the finite intersections into `X`. A
chosen refinement induces a functor between index categories and a natural map of Čech diagrams.

## References

* R. Brown, *Topology and Groupoids*, Chapters 6--7.
* T. Zhu, [mathlib4#41603](https://github.com/leanprover-community/mathlib4/pull/41603), whose
  open-set and fundamental-groupoid object and map shapes guide this interface.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

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
lemma mem_cechIntersection (x : X) (s : CechIndex ι) :
    x ∈ cechIntersection U s ↔ ∀ i ∈ s.1, x ∈ U i := by
  classical
  unfold cechIntersection
  induction s.1 using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.inf_insert, ih]

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
    eqToHom (cechTopDiagram_obj U t)
        ((cechTopDiagram U).map f (eqToHom (cechTopDiagram_obj U s).symm x)) =
      ⟨x.1, cechIntersection_mono U f.le x.2⟩ := by
  exact Opens.toTopCat_map X (f := (cechOpenDiagram U).map f)

/-- The inclusion of a finite-family intersection into the ambient space. -/
def cechInclusion (s : CechIndex ι) : (cechTopDiagram U).obj s ⟶ X :=
  Opens.inclusion' (cechIntersection U s)

@[simp]
lemma cechInclusion_apply (s : CechIndex ι) (x : TopCat.of (cechIntersection U s)) :
    cechInclusion U s (eqToHom (cechTopDiagram_obj U s).symm x) = x.1 := by
  exact congrFun Opens.coe_inclusion' x

@[simp, reassoc]
lemma cechTopDiagram_map_comp_inclusion {s t : CechIndex ι} (f : s ⟶ t) :
    (cechTopDiagram U).map f ≫ cechInclusion U t = cechInclusion U s := by
  ext x
  exact (cechInclusion_apply U t _).trans (congrArg Subtype.val (cechTopDiagram_map_apply U f x))

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

/-! ### Refinements -/

namespace CechIndex

private noncomputable def image {ι : Type u} {κ : Type w} (r : ι → κ) (s : Finset ι) :
    Finset κ := by
  classical
  exact s.image r

private lemma image_mono {ι : Type u} {κ : Type w} (r : ι → κ) :
    Monotone (image r) := by
  classical
  exact Finset.image_mono r

private lemma image_nonempty {ι : Type u} {κ : Type w} {r : ι → κ} {s : Finset ι}
    (hs : s.Nonempty) : (image r s).Nonempty := by
  classical
  exact hs.image r

/-- The functor on Čech index categories induced by a map of indexing types. It sends a nonempty
finite set to its image. -/
noncomputable def map {ι : Type u} {κ : Type w} (r : ι → κ) :
    CechIndex.{u} ι ⥤ CechIndex.{w} κ :=
  { obj := fun s ↦ OrderDual.toDual ⟨image r s.1, image_nonempty s.2⟩
    map := fun f ↦ homOfLE (image_mono r f.le)
    map_id := fun _ ↦ Subsingleton.elim _ _
    map_comp := fun _ _ ↦ Subsingleton.elim _ _ }

@[simp]
lemma mem_map_obj_iff {ι : Type u} {κ : Type w} (r : ι → κ) (s : CechIndex ι) (j : κ) :
    j ∈ ((map r).obj s).1 ↔ ∃ i ∈ s.1, r i = j := by
  classical
  change j ∈ s.1.image r ↔ _
  exact Finset.mem_image

@[simp]
lemma map_obj_singleton {ι : Type u} {κ : Type w} (r : ι → κ) (i : ι) :
    (map r).obj (singleton i) = singleton (r i) := by
  classical
  apply Subtype.ext
  ext j
  simp [eq_comm]

end CechIndex

section Refinement

variable {X : TopCat.{v}} {ι : Type u} {κ : Type w} (U : ι → Opens X) (V : κ → Opens X)
  (r : ι → κ) (hr : ∀ i, U i ≤ V (r i))

include hr

/-- The intersection indexed by `s` in a finer family is contained in the intersection indexed
by the image of `s` in a coarser family. -/
lemma cechIntersection_le_refinement (s : CechIndex ι) :
    cechIntersection U s ≤ cechIntersection V ((CechIndex.map r).obj s) := by
  classical
  intro x hx
  rw [mem_cechIntersection] at hx ⊢
  intro j hj
  rw [CechIndex.mem_map_obj_iff] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact hr i (hx i hi)

/-- The inclusion from an intersection in a finer family to the corresponding intersection in a
coarser family. -/
def cechRefinement (s : CechIndex ι) :
    (cechTopDiagram U).obj s ⟶ (cechTopDiagram V).obj ((CechIndex.map r).obj s) :=
  (Opens.toTopCat X).map (homOfLE (cechIntersection_le_refinement U V r hr s))

/-- Refinement inclusions commute with the canonical inclusions of Čech intersections into the
ambient space. -/
@[reassoc]
lemma cechRefinement_comp_inclusion (s : CechIndex ι) :
    cechRefinement U V r hr s ≫ cechInclusion V ((CechIndex.map r).obj s) =
      cechInclusion U s := by
  ext x
  rfl

/-- The inclusions associated to a chosen refinement form a natural transformation between the
two topological Čech diagrams. -/
def cechRefinementNatTrans :
    cechTopDiagram U ⟶ CechIndex.map r ⋙ cechTopDiagram V where
  app := cechRefinement U V r hr
  naturality _ _ _ := by
    ext x
    rfl

@[simp]
lemma cechRefinementNatTrans_app (s : CechIndex ι) :
    (cechRefinementNatTrans U V r hr).app s = cechRefinement U V r hr s := (rfl)

end Refinement

end TauCeti.TopCat
