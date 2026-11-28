/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Basic
public import TauCeti.AlgebraicGeometry.Neron.MappingProperty
import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
import TauCeti.AlgebraicGeometry.Blowup.Restriction
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Basic
import TauCeti.AlgebraicGeometry.Pullback.Over
import TauCeti.AlgebraicGeometry.Restrict

/-!
# An obstruction to the Néron mapping property for blowups

Let `X ⟶ S` be smooth and separated and let the blowup of `X` be locally of finite
presentation over `S`. If an open immersion into `S` has schematically dense pullback in
`X` disjoint from the non-Cartier centre, the smooth locus of the blowup fails the Néron
mapping property for that immersion. The inverse to the blowup over the open cannot
extend from the original smooth scheme.

The argument uses Mathlib's restriction and smooth locus, and Tau Ceti's schematic
density criterion for equality of morphisms into a separated scheme and the effective
Cartier exceptional divisor of a blowup.

## Main results

* `Scheme.IdealSheafData.not_neronMappingProperty_smoothLocus_blowup` gives the
  non-extension obstruction.

## References

* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §1.2, Definition 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Neron

/-- Let `X` be smooth and separated over `S`, with blowup locally of finite presentation
over `S`. Let `j : η ⟶ S` be an open immersion whose inverse image in `X` is schematically
dense. If the centre misses that inverse image and is not effective Cartier, the smooth
locus of the blowup fails the Néron mapping property relative to `j`. The original scheme
`X` is the smooth test object from which the generic inverse cannot extend. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.not_neronMappingProperty_smoothLocus_blowup
    {η X S : Scheme.{u}} (I : X.IdealSheafData) {f : X ⟶ S} [Smooth f] [IsSeparated f]
    (j : η ⟶ S) [IsOpenImmersion j] [IsSchemeTheoreticallyDominant (pullback.fst f j)]
    [LocallyOfFinitePresentation (I.blowupToBase ≫ f)]
    (hV : Disjoint (↑(f ⁻¹ᵁ j.opensRange) : Set X) (↑I.support : Set X))
    (hI : ¬ I.IsEffectiveCartier) :
    ¬ NeronMappingProperty j
      (Over.mk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase ≫ f)) := by
  let b := I.blowupToBase
  let U := (b ≫ f).smoothLocus
  let m : Over.mk (U.ι ≫ b ≫ f) ⟶ Over.mk f :=
    Over.homMk (U.ι ≫ b) (Category.assoc _ _ _)
  have hmLeft : m.left = U.ι ≫ b := by simp only [m, Over.homMk_left]
  have hb : IsIso (b ∣_ f ⁻¹ᵁ j.opensRange) :=
    I.isIso_blowupToBase_restrict_of_disjoint_support hV
  have hres : Smooth ((b ≫ f) ∣_ j.opensRange) := by
    rw [morphismRestrict_comp]
    exact inferInstanceAs (Smooth ((b ∣_ f ⁻¹ᵁ j.opensRange) ≫ (f ∣_ j.opensRange)))
  -- Over the base open the blowup is smooth, so passing to its smooth locus loses nothing.
  have hU : b ⁻¹ᵁ (f ⁻¹ᵁ j.opensRange) ≤ U := by
    rw [← Scheme.Hom.comp_preimage]
    exact (b ≫ f).preimage_le_smoothLocus_of_smooth_restrict _ hres
  have hm : IsIso ((Over.pullback j).map m) := by
    rw [m.isIso_pullback_map_iff_of_isOpenImmersion j, hmLeft]
    simp only [Over.mk_hom, morphismRestrict_comp]
    have hi : IsIso (U.ι ∣_ b ⁻¹ᵁ (f ⁻¹ᵁ j.opensRange)) :=
      U.ι.isIso_morphismRestrict_of_le_opensRange (by rwa [Scheme.Opens.opensRange_ι])
    exact IsIso.comp_isIso' hi hb
  intro h
  have hd : IsSchemeTheoreticallyDominant (pullback.fst (Over.mk f).hom j) := by
    simpa only [Over.mk_hom] using
      (inferInstance : IsSchemeTheoreticallyDominant (pullback.fst f j))
  have hs : IsSeparated (Over.mk f).hom := by
    simpa only [Over.mk_hom] using (inferInstance : IsSeparated f)
  have hY : Smooth (Over.mk f).hom := by
    simpa only [Over.mk_hom] using (inferInstance : Smooth f)
  have : IsSplitEpi m := h.isSplitEpi_of_isSplitEpi_pullback_map m hY
  have hsec : ((section_ m).left ≫ U.ι) ≫ b = 𝟙 X := by
    simpa only [Over.comp_left, Over.id_left, hmLeft, Category.assoc, Over.mk_left]
      using congrArg Over.Hom.left (IsSplitEpi.id m)
  exact hI (I.isSplitEpi_blowupToBase_iff.mp (IsSplitEpi.mk' ⟨(section_ m).left ≫ U.ι, hsec⟩))

end TauCeti.AlgebraicGeometry.Neron
