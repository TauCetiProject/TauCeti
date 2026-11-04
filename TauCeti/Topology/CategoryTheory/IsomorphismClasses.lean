/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.Combinatorics.Quiver.Subquiver
public import Mathlib.Topology.Compactness.Paracompact

/-!
# The coarse topology of a groupoid

The coarse space of a categorical groupoid is the native quotient of its objects by
`CategoryTheory.isIsomorphicSetoid`, with the quotient topology. A continuous source and an
open target make the quotient projection open. A closed source-target range then makes the
coarse space Hausdorff. In particular these conclusions apply to proper étale presentations.
No topology on individual hom types, and no replacement groupoid carrier, is needed.

Second countability and local compactness descend along the open quotient by
`Topology.IsOpenQuotientMap.secondCountableTopology` and
`Topology.IsOpenQuotientMap.locallyCompactSpace`. Together with Hausdorffness, these give
paracompactness when the object space is locally compact and second countable. This is the
topology needed for partitions of unity and locally finite covers on an orbifold coarse space.
The hypotheses concern actual total arrows; ineffective isotropy is not removed.

## References

* I. Moerdijk, *Orbifolds as groupoids: an introduction*, Section 2.
-/

public section

open CategoryTheory Set Topology

namespace TauCeti

variable {C : Type*} [Groupoid C]

/-- Two objects have the same isomorphism class exactly when there is an arrow between them. -/
theorem isomorphismClassesMk_eq_iff {x y : C} :
    Quotient.mk (isIsomorphicSetoid C) x = Quotient.mk (isIsomorphicSetoid C) y ↔
      Nonempty (x ⟶ y) :=
  Quotient.eq.trans Groupoid.isIsomorphic_iff_nonempty_hom

/-- Saturating a set of objects amounts to taking targets of arrows with source in the set. -/
theorem isomorphismClasses_preimage_image_eq {U : Set C} :
    Quotient.mk (isIsomorphicSetoid C) ⁻¹' (Quotient.mk (isIsomorphicSetoid C) '' U) =
      Quiver.Total.right '' (Quiver.Total.left ⁻¹' U) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨f⟩ := isomorphismClassesMk_eq_iff.mp hxy
    exact ⟨⟨x, y, f⟩, hx, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a.left, ha, isomorphismClassesMk_eq_iff.mpr ⟨a.hom⟩⟩

/-- The relation of having equal isomorphism classes is the range of the source-target map. -/
theorem setOf_isomorphismClassesMk_eq_eq_range :
    {p : C × C | Quotient.mk (isIsomorphicSetoid C) p.1 =
      Quotient.mk (isIsomorphicSetoid C) p.2} =
      Set.range (fun a : Quiver.Total C ↦ (a.left, a.right)) := by
  ext p
  constructor
  · intro h
    obtain ⟨f⟩ := isomorphismClassesMk_eq_iff.mp h
    exact ⟨⟨p.1, p.2, f⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    exact isomorphismClassesMk_eq_iff.mpr ⟨a.hom⟩

variable [TopologicalSpace C] [TopologicalSpace (Quiver.Total C)]

/-- With continuous source and open target, the projection to isomorphism classes is an
open quotient map. Local homeomorphisms satisfy both hypotheses. -/
theorem isOpenQuotientMap_isomorphismClassesMk
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsOpenMap (Quiver.Total.right : Quiver.Total C → C)) :
    IsOpenQuotientMap (Quotient.mk (isIsomorphicSetoid C)) := by
  refine .of_isOpenMap_isQuotientMap ?_ isQuotientMap_quotient_mk'
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  -- The quotient-map API uses Quotient.mk'; normalize to Quotient.mk for the saturation lemma.
  change IsOpen (Quotient.mk (isIsomorphicSetoid C) ⁻¹'
    (Quotient.mk (isIsomorphicSetoid C) '' U))
  rw [isomorphismClasses_preimage_image_eq]
  exact ht _ (hU.preimage hs)

/-- A groupoid with continuous source, open target and closed source-target range has a
Hausdorff coarse quotient. Properness of the source-target map is sufficient; neither the
objects nor arrows need an additional separation hypothesis here. -/
theorem t2Space_isomorphismClasses
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsOpenMap (Quiver.Total.right : Quiver.Total C → C))
    (hc : IsClosed (Set.range fun a : Quiver.Total C ↦ (a.left, a.right))) :
    T2Space (Quotient (isIsomorphicSetoid C)) := by
  rw [t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_isomorphismClassesMk hs ht),
    setOf_isomorphismClassesMk_eq_eq_range]
  exact hc

/-- The coarse quotient of a locally compact, second-countable groupoid is paracompact
when source is continuous, target is open and the source-target range is closed. In particular
this applies to Hausdorff second-countable proper étale manifold presentations. -/
theorem paracompactSpace_isomorphismClasses [LocallyCompactSpace C] [SecondCountableTopology C]
    (hs : Continuous (Quiver.Total.left : Quiver.Total C → C))
    (ht : IsOpenMap (Quiver.Total.right : Quiver.Total C → C))
    (hc : IsClosed (Set.range fun a : Quiver.Total C ↦ (a.left, a.right))) :
    ParacompactSpace (Quotient (isIsomorphicSetoid C)) := by
  have hq := isOpenQuotientMap_isomorphismClassesMk hs ht
  let := hq.locallyCompactSpace
  let := hq.secondCountableTopology
  let := t2Space_isomorphismClasses hs ht hc
  infer_instance

end TauCeti
