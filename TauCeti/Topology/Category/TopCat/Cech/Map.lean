/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Cech.Refinement
import all TauCeti.Topology.Category.TopCat.Cech.Diagram

/-!
# Maps of topological Čech diagrams

A continuous map between spaces, together with a map of cover indices that carries each source
open into the corresponding target open, induces a natural transformation between their Čech
diagrams.  The transformation commutes with the canonical inclusions of the intersections into
the ambient spaces.

These maps provide the topological input for naturality of constructions obtained by applying a
functor to a Čech diagram, in particular the fundamental-groupoid van Kampen cocone.

## References

* R. Brown, *Topology and Groupoids*, Chapters 6--7.
-/

public section

noncomputable section

open CategoryTheory Set TopologicalSpace

universe u v z

namespace TauCeti.TopCat

variable {X Y : TopCat.{v}} {ι : Type u} {κ : Type z}
  (U : ι → Opens X) (V : κ → Opens Y) (f : X ⟶ Y) (r : ι → κ)
  (hf : ∀ i, MapsTo f (U i) (V (r i)))

include hf

/-- A map of covered spaces carries an intersection in the source Čech diagram into the
intersection indexed by the corresponding image in the target diagram. -/
lemma mapsTo_cechIntersection (s : CechIndex ι) :
    MapsTo f (cechIntersection U s) (cechIntersection V ((CechIndex.map r).obj s)) := by
  classical
  intro x hx
  refine (mem_cechIntersection V (f x) _).2 ?_
  intro j hj
  rw [CechIndex.mem_map_obj_iff] at hj
  obtain ⟨i, hi, rfl⟩ := hj
  exact hf i ((mem_cechIntersection U x s).1 hx i hi)

/-- The map between two Čech intersections induced by a map of covered spaces. -/
def cechMap (s : CechIndex ι) :
    (cechTopDiagram U).obj s ⟶ (cechTopDiagram V).obj ((CechIndex.map r).obj s) :=
  TopCat.ofHom
    { toFun := fun x ↦ ⟨f x.1, mapsTo_cechIntersection U V f r hf s x.2⟩
      continuous_toFun := (f.hom.continuous.comp continuous_subtype_val).subtype_mk _ }

@[simp]
lemma cechMap_apply (s : CechIndex ι) (x : TopCat.of (cechIntersection U s)) :
    eqToHom (cechTopDiagram_obj V ((CechIndex.map r).obj s))
        (cechMap U V f r hf s
          (eqToHom (cechTopDiagram_obj U s).symm x)) =
      ⟨f x.1, mapsTo_cechIntersection U V f r hf s x.2⟩ := (rfl)

/-- Maps between Cech intersections commute with their inclusions into the ambient spaces. -/
@[reassoc]
lemma cechMap_comp_inclusion (s : CechIndex ι) :
    cechMap U V f r hf s ≫ cechInclusion V ((CechIndex.map r).obj s) =
      cechInclusion U s ≫ f := by
  ext x
  rfl

/-- The intersection maps associated to a map of covered spaces form a natural transformation
between the two Čech diagrams. -/
def cechMapNatTrans :
    cechTopDiagram U ⟶ CechIndex.map r ⋙ cechTopDiagram V where
  app := cechMap U V f r hf
  naturality _ t g := by
    have : Mono (cechInclusion V ((CechIndex.map r).obj t)) :=
      (TopCat.mono_iff_injective _).2 Subtype.val_injective
    rw [← cancel_mono (cechInclusion V ((CechIndex.map r).obj t))]
    simp only [Category.assoc, cechMap_comp_inclusion, Functor.comp_map]
    rw [cechTopDiagram_map_comp_inclusion]
    exact (cechMap_comp_inclusion U V f r hf _).symm

@[simp]
lemma cechMapNatTrans_app (s : CechIndex ι) :
    (cechMapNatTrans U V f r hf).app s = cechMap U V f r hf s := (rfl)

end TauCeti.TopCat
