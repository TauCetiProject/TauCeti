/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Cech.Diagram
import all TauCeti.Topology.Category.TopCat.Cech.Diagram

/-!
# Refinements of topological Čech diagrams

A map of indexing types `r : ι → κ` induces a functor between Čech index categories, sending a
nonempty finite set to its image. If `U i ⊆ V (r i)` for all `i`, the inclusions of each finite
intersection for `U` into the intersection for the image of its indices form a natural
transformation between the topological Čech diagrams, compatible with the inclusions into the
ambient space.

## References

* R. Brown, *Topology and Groupoids*, Chapters 6--7.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u v w

namespace TauCeti.TopCat

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
  exact Finset.mem_image (s := s.1) (f := r)

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
  exact (cechInclusion_apply V _ (cechRefinement U V r hr s x)).trans
    (cechInclusion_apply U s x).symm

/-- The inclusions associated to a chosen refinement form a natural transformation between the
two topological Čech diagrams. -/
def cechRefinementNatTrans :
    cechTopDiagram U ⟶ CechIndex.map r ⋙ cechTopDiagram V where
  app := cechRefinement U V r hr
  naturality _ t f := by
    have : Mono (cechInclusion V ((CechIndex.map r).obj t)) :=
      (TopCat.mono_iff_injective _).2 Subtype.val_injective
    rw [← cancel_mono (cechInclusion V ((CechIndex.map r).obj t))]
    simp only [Category.assoc, cechRefinement_comp_inclusion, Functor.comp_map,
      cechTopDiagram_map_comp_inclusion]

@[simp]
lemma cechRefinementNatTrans_app (s : CechIndex ι) :
    (cechRefinementNatTrans U V r hr).app s = cechRefinement U V r hr s := (rfl)

end Refinement

end TauCeti.TopCat
