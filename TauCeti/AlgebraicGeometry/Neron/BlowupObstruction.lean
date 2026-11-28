/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Neron.MappingProperty
public import TauCeti.AlgebraicGeometry.Pullback.Over
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Basic
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.CategoryTheory.IrreducibleMorphism

/-!
# An obstruction to the Néron mapping property for blowups

For a smooth separated scheme over a base, an inverse to the blowup over a schematically
dense base open cannot extend to the smooth locus when the centre is not effective Cartier.
`Scheme.IdealSheafData.not_surjective_pullback_map_smoothLocus_blowup` gives this failure
of extension, and `Scheme.IdealSheafData.not_neronMappingProperty_smoothLocus_blowup` applies it
to the Néron mapping property. The proof uses Mathlib's smooth locus and Tau Ceti's section
criterion `Scheme.IdealSheafData.isSplitEpi_blowupToBase_iff`.

## References

* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §1.2, Definition 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry.Neron

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {η X S : Scheme.{u}} {f : X ⟶ S} [Smooth f] [IsSeparated f]
  (I : X.IdealSheafData) (j : η ⟶ S) [IsOpenImmersion j]
  [IsSchemeTheoreticallyDominant (pullback.fst f j)]
  [LocallyOfFinitePresentation (I.blowupToBase ≫ f)]

/-- If the blowup is an isomorphism over the schematically dense base open and its centre
is not effective Cartier, base change is not surjective on maps from the original smooth
scheme to the smooth locus of the blowup. -/
theorem not_surjective_pullback_map_smoothLocus_blowup
    (hb : IsIso (I.blowupToBase ∣_ f ⁻¹ᵁ j.opensRange)) (hI : ¬ I.IsEffectiveCartier) :
    ¬ Function.Surjective ((Over.pullback j).map :
      (Over.mk f ⟶ Over.mk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase ≫ f)) → _) := by
  let b := I.blowupToBase
  let U := (b ≫ f).smoothLocus
  let m : Over.mk (U.ι ≫ b ≫ f) ⟶ Over.mk f := Over.homMk (U.ι ≫ b) (Category.assoc _ _ _)
  have hmLeft : m.left = U.ι ≫ b := by simp only [m, Over.homMk_left]
  have hb' : IsIso (b ∣_ f ⁻¹ᵁ j.opensRange) := hb
  have hres : Smooth ((b ≫ f) ∣_ j.opensRange) := by
    rw [morphismRestrict_comp]
    exact inferInstanceAs (Smooth ((b ∣_ f ⁻¹ᵁ j.opensRange) ≫ (f ∣_ j.opensRange)))
  -- Over the base open the blowup is smooth, so passing to its smooth locus loses nothing.
  have hU : b ⁻¹ᵁ (f ⁻¹ᵁ j.opensRange) ≤ U := by
    rw [← Scheme.Hom.comp_preimage]
    exact (b ≫ f).preimage_le_smoothLocus_of_smooth_morphismRestrict _ hres
  have hm : IsIso ((Over.pullback j).map m) := by
    rw [m.isIso_pullback_map_iff_of_isOpenImmersion j, hmLeft]
    simp only [Over.mk_hom, morphismRestrict_comp]
    have hi : IsIso (U.ι ∣_ b ⁻¹ᵁ (f ⁻¹ᵁ j.opensRange)) :=
      U.ι.isIso_morphismRestrict_of_le_opensRange (by rwa [Scheme.Opens.opensRange_ι])
    exact IsIso.comp_isIso' hi hb
  intro h
  have hd : IsSchemeTheoreticallyDominant (pullback.fst (Over.mk f).hom j) :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.fst f j))
  have hs : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : IsSplitEpi m := m.isSplitEpi_of_surjective_pullback_map h
  have hc : IsSplitEpi (U.ι ≫ b) := by
    simpa only [Over.forget_map, hmLeft] using
      (inferInstance : IsSplitEpi ((Over.forget S).map m))
  exact hI (I.isSplitEpi_blowupToBase_iff.mp (TauCeti.isSplitEpi_of_isSplitEpi_comp U.ι b))

/-- The smooth locus of the blowup fails the Néron mapping property if the centre is not
effective Cartier and the blowup is an isomorphism over the schematically dense base open.
For a disjoint centre, use `isIso_blowupToBase_restrict_of_disjoint_support`. -/
theorem not_neronMappingProperty_smoothLocus_blowup
    (hb : IsIso (I.blowupToBase ∣_ f ⁻¹ᵁ j.opensRange)) (hI : ¬ I.IsEffectiveCartier) :
    ¬ NeronMappingProperty j
      (Over.mk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase ≫ f)) :=
  MappingProperty.not_of_not_surjective (Over.mk f) (inferInstanceAs (Smooth f))
    (I.not_surjective_pullback_map_smoothLocus_blowup j hb hI)

end AlgebraicGeometry.Scheme.IdealSheafData
