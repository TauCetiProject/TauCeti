/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Neron.MappingProperty
public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Over

/-!
# An obstruction to the Néron mapping property for blowups

`Scheme.IdealSheafData.not_neronMappingProperty_smoothLocus_blowup` applies
`Scheme.Hom.isIso_pullback_map_smoothLocus` to identify the base-changed projection from the
smooth locus of a blowup over a base open. Its inverse cannot extend if the original scheme
is separated, the base change is schematically dense, and the centre is not effective Cartier,
by `Scheme.IdealSheafData.section_pullback_map_not_mem_range_of_not_isEffectiveCartier`.

## References

* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §1.2, Definition 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry.Neron

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {η X S : Scheme.{u}} {f : X ⟶ S} (I : X.IdealSheafData)
  [LocallyOfFinitePresentation (I.blowupToBase ≫ f)]

variable (j : η ⟶ S)

/-- The smooth locus of the blowup fails the Néron mapping property if the centre is not
effective Cartier and the blowup is an isomorphism over the schematically dense base open.
For a disjoint centre, use `isIso_blowupToBase_restrict_of_disjoint_support`. -/
theorem not_neronMappingProperty_smoothLocus_blowup [Smooth f] [IsSeparated f]
    [IsOpenImmersion j] [IsSchemeTheoreticallyDominant (pullback.fst f j)]
    (hb : IsIso (I.blowupToBase ∣_ f ⁻¹ᵁ j.opensRange)) (hI : ¬ I.IsEffectiveCartier) :
    ¬ NeronMappingProperty j
      (Over.mk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase ≫ f)) := by
  have hs : Smooth (Over.mk f).hom := by
    simpa only [Over.mk_hom] using (inferInstance : Smooth f)
  have hi := I.blowupToBase.isIso_pullback_map_smoothLocus j
    (inferInstance : Smooth (f ∣_ j.opensRange)) hb
  exact MappingProperty.not_of_not_surjective (Over.mk f) hs fun h ↦
    I.section_pullback_map_not_mem_range_of_not_isEffectiveCartier j
      (p := (I.blowupToBase ≫ f).smoothLocus.ι) (IsIso.inv_hom_id _) hI (h _)

end AlgebraicGeometry.Scheme.IdealSheafData
