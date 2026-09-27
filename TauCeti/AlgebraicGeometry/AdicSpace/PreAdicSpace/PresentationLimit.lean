/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.StructurePresheaf.Stalk.LocalRing

/-!
# The presentation-limit pre-adic space

The adic spectrum with its presentation-limit presheaf is a pre-adic space when the plus
subring consists of power-bounded elements and contains a ring of definition.
This packages the structure presheaf, local stalks, and residue valuations into a
pre-adic-space object on the adic spectrum for later morphism and sheafiness constructions.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace TauCeti.ValuationSpectrum

open TauCeti.Huber

universe u

/-- The pre-adic space of an adic spectrum with the completed rational-localisation presheaf.
The valuation at a point is induced on the residue field of its local stalk. -/
noncomputable def presentationLimitPreAdicSpace {A : Type u} [CommRing A]
    [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) : PreAdicSpace.{u} where
  toPresheafedSpace :=
    { carrier := TopCat.of ↥(spa Aplus)
      presheaf := presentationLimitPresheaf P Aplus }
  isLocalRing x := by
    have e := presentationLimitPresheafInCommRingCat_def P Aplus
    rw [Functor.mapPresheaf_obj_presheaf, ← e]
    exact isLocalRing_stalk_presentationLimitPresheafInCommRingCat hAplus hP x
  valuation x := by
    have e := presentationLimitPresheafInCommRingCat_def P Aplus
    -- This transports both the stalk and its local-ring instance in the residue-field type.
    cases e
    exact presentationLimitStalkResidueValuation hAplus hP x

/-- The space underlying the presentation-limit pre-adic space is its adic spectrum. -/
@[simp]
theorem presentationLimitPreAdicSpace_carrier {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) :
    ((presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace : TopCat) =
      TopCat.of ↥(spa Aplus) :=
  (rfl)

/-- The sections of this pre-adic space form the presentation-limit presheaf. -/
@[simp]
theorem presentationLimitPreAdicSpace_presheaf {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) :
    @HEq ((presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace.carrier.Presheaf
      CompleteSeparatedTopCommRingCat.{u})
      (presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace.presheaf
      ((TopCat.of ↥(spa Aplus)).Presheaf CompleteSeparatedTopCommRingCat.{u})
      (presentationLimitPresheaf P Aplus) :=
  HEq.rfl

/-- Forgetting the topology gives the presentation-limit presheaf of rings. -/
@[simp]
theorem presentationLimitPreAdicSpace_ringPresheaf {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) :
    @HEq ((presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace.carrier.Presheaf
      CommRingCat.{u})
      ((presentationLimitPreAdicSpace P Aplus hAplus hP).toPresheafedSpace.presheaf ⋙
        TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat)
      ((TopCat.of ↥(spa Aplus)).Presheaf CommRingCat.{u})
      (presentationLimitPresheaf P Aplus ⋙
        TopCommRingCat.isCompleteSeparated.ι ⋙ forget₂ TopCommRingCat CommRingCat) :=
  HEq.rfl

/-- The valuation of a presentation-limit pre-adic space is the stalk residue valuation. -/
@[simp]
theorem presentationLimitPreAdicSpace_valuation {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hAplus : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a)
    (hP : P.ringOfDefinition ≤ Aplus) (x : spa Aplus) :
    HEq ((presentationLimitPreAdicSpace P Aplus hAplus hP).valuation
      ((presentationLimitPreAdicSpace_carrier P Aplus hAplus hP).symm ▸ x))
      (presentationLimitStalkResidueValuation hAplus hP x) :=
  by
    let e := presentationLimitPresheafInCommRingCat_def P Aplus
    -- Transport the stalk and its local-ring instance together in the residue-field type.
    cases e
    exact HEq.rfl

end TauCeti.ValuationSpectrum

end
