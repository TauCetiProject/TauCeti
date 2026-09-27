/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalk.LocalRing
public import TauCeti.Topology.Category.TopCommRingCat.CompleteSeparated.Basic

/-!
# Pre-adic spaces

A pre-adic space has a presheaf of complete separated topological rings, local ring stalks,
and a valuation on the residue field at every point. The valuation is a point of the valuation
spectrum, so it is specified only up to equivalence. Stalks and residue fields are taken after
forgetting the topology on the rings; no topology is imposed on a stalk.

The adic spectrum equipped with its presentation-limit presheaf supplies a pre-adic space when
the plus subring consists of power-bounded elements and contains a ring of definition. This
construction gathers the local ring and residue valuation already attached
to its stalks into one object. It is the object-level input for morphisms of pre-adic spaces and
for the sheafy full subcategory.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, §8.1.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti

universe u

/-- A topological space with a presheaf of complete separated topological commutative rings,
local stalks, and a valuation on each stalk's residue field. The underlying ring presheaf is
recorded with an equality to the result of forgetting topology, so stalk constructions use the
category of rings. -/
structure PreAdicSpace where
  /-- The underlying topological space. -/
  carrier : TopCat.{u}
  /-- The presheaf of complete separated topological rings. -/
  presheaf : carrier.Presheaf CompleteSeparatedTopCommRingCat.{u}
  /-- The underlying presheaf of commutative rings. -/
  ringPresheaf : carrier.Presheaf CommRingCat.{u}
  /-- The ring presheaf is obtained by forgetting topology. -/
  ringPresheaf_eq : ringPresheaf = presheaf ⋙ TopCommRingCat.isCompleteSeparated.ι ⋙
    forget₂ TopCommRingCat CommRingCat
  /-- Every stalk of the underlying ring presheaf is local. -/
  isLocalRing : ∀ x : carrier, IsLocalRing (ringPresheaf.stalk x)
  /-- The valuation of the residue field at each point. -/
  valuation : ∀ x : carrier,
    letI := isLocalRing x
    ValuationSpectrum (IsLocalRing.ResidueField (ringPresheaf.stalk x))

namespace PreAdicSpace

/-- The underlying presheafed space of a pre-adic space. -/
noncomputable def toPresheafedSpace (X : PreAdicSpace.{u}) :
    AlgebraicGeometry.PresheafedSpace CommRingCat.{u} where
  carrier := X.carrier
  presheaf := X.ringPresheaf

end PreAdicSpace

end TauCeti

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

/-- The pre-adic space of an adic spectrum with the completed rational-localisation presheaf.
The valuation at a point is induced on the residue field of its local stalk. -/
noncomputable def presentationLimitPreAdicSpace {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) : PreAdicSpace.{u} where
  carrier := TopCat.of ↥(spa Aplus)
  presheaf := presentationLimitPresheaf P Aplus
  ringPresheaf := presentationLimitPresheafInCommRingCat P Aplus
  ringPresheaf_eq := presentationLimitPresheafInCommRingCat_def P Aplus
  isLocalRing x := isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
  valuation x := presentationLimitStalkResidueValuation hAplus hP x

/-- The space underlying the presentation-limit pre-adic space is its adic spectrum. -/
@[simp]
theorem presentationLimitPreAdicSpace_carrier {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) :
    (presentationLimitPreAdicSpace P Aplus hAplus hP).carrier = TopCat.of ↥(spa Aplus) :=
  (rfl)

/-- The sections of this pre-adic space form the presentation-limit presheaf. -/
theorem presentationLimitPreAdicSpace_presheaf {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) :
    @HEq ((presentationLimitPreAdicSpace P Aplus hAplus hP).carrier.Presheaf
      CompleteSeparatedTopCommRingCat.{u})
      (presentationLimitPreAdicSpace P Aplus hAplus hP).presheaf
      ((TopCat.of ↥(spa Aplus)).Presheaf CompleteSeparatedTopCommRingCat.{u})
      (presentationLimitPresheaf P Aplus) :=
  (HEq.rfl)

end TauCeti.ValuationSpectrum

end
