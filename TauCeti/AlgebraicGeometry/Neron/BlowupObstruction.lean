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
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.AlgebraicGeometry.Morphisms.Smooth.Locus.Basic
import TauCeti.AlgebraicGeometry.Restrict
import TauCeti.CategoryTheory.Comma.Over.Pullback

/-!
# An obstruction to the Néron mapping property for blowups

The smooth locus of a blowup of a smooth separated scheme in a non-Cartier vertical
centre fails the full Néron mapping property. The test scheme is the original smooth
scheme. The inverse to the blowup over the base open cannot extend.

The argument uses Mathlib's restriction and smooth locus, and Tau Ceti's schematic
density criterion for equality of morphisms into a separated scheme and the effective
Cartier exceptional divisor of a blowup.

## Main results

* `MappingProperty.isSplitEpi_of_pullback` extends a section of a generic
  morphism when its target is a test object with schematically dense generic fibre.
* `Scheme.IdealSheafData.not_neronMappingProperty_smoothLocus_blowup` gives the
  non-extension obstruction.

## References

* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §1.2, Definition 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.Neron

/-- Under the mapping property for `P`, a morphism with split-epimorphic restriction to
`η` admits a section if its target is a separated test object and the base change is
schematically dense in that target. -/
theorem MappingProperty.isSplitEpi_of_pullback
    {P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop} {η S : Scheme.{u}} {j : η ⟶ S}
    {X Y : Over S} (h : MappingProperty P j X) (f : X ⟶ Y) (hY : P Y.hom)
    [IsSeparated Y.hom] [IsSchemeTheoreticallyDominant (pullback.fst Y.hom j)]
    [IsSplitEpi ((Over.pullback j).map f)] :
    IsSplitEpi f := by
  obtain ⟨g, hg⟩ := h.surjective Y hY (section_ ((Over.pullback j).map f))
  refine IsSplitEpi.mk' ⟨g, ?_⟩
  have heq : (Over.pullback j).map (g ≫ f) = (Over.pullback j).map (𝟙 Y) := by
    rw [Functor.map_comp, hg, IsSplitEpi.id]
    exact ((Over.pullback j).map_id Y).symm
  apply Over.OverMorphism.ext
  exact ext_of_isSchemeTheoreticallyDominant (pullback.fst Y.hom j) Y.hom
    (by simp only [Over.comp_left, Category.assoc, Over.w, Over.id_left, Category.id_comp])
    ((Over.pullback_map_eq_map_iff j _ _).mp heq)

/-- Let `X` be smooth and separated over `S`, and let `V` be an open of `S` whose inverse
image in `X` is schematically dense. If the blowup centre misses that inverse image and is
not an effective Cartier divisor, the smooth locus of the blowup fails the Néron mapping
property relative to `V.ι`. The original scheme `X` is the smooth test object for which
the inverse to the generic restriction of the blowup does not extend. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.not_neronMappingProperty_smoothLocus_blowup
    {X S : Scheme.{u}} (I : X.IdealSheafData) {f : X ⟶ S} [Smooth f] [IsSeparated f]
    (V : S.Opens) [IsSchemeTheoreticallyDominant (pullback.fst f V.ι)]
    [LocallyOfFinitePresentation (I.blowupToBase ≫ f)]
    (hV : Disjoint (↑(f ⁻¹ᵁ V) : Set X) (↑I.support : Set X))
    (hI : ¬ I.IsEffectiveCartier) :
    ¬ NeronMappingProperty V.ι
      (Over.mk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase ≫ f)) := by
  let b := I.blowupToBase
  let U := (b ≫ f).smoothLocus
  let m : Over.mk (U.ι ≫ b ≫ f) ⟶ Over.mk f :=
    Over.homMk (U.ι ≫ b) (Category.assoc _ _ _)
  have hb : IsIso (b ∣_ f ⁻¹ᵁ V) := I.isIso_blowupToBase_restrict_of_disjoint_support hV
  -- Over `V` the blowup is still smooth, so passing to its smooth locus loses nothing there.
  have hU : b ⁻¹ᵁ (f ⁻¹ᵁ V) ≤ U := by
    rw [← Scheme.Hom.comp_preimage]
    apply ((b ≫ f).smooth_ι_comp_iff_le_smoothLocus _).mp
    rw [← morphismRestrict_ι]
    have hres : Smooth ((b ≫ f) ∣_ V) := by
      rw [morphismRestrict_comp]
      exact inferInstanceAs (Smooth ((b ∣_ f ⁻¹ᵁ V) ≫ (f ∣_ V)))
    exact inferInstanceAs (Smooth (((b ≫ f) ∣_ V) ≫ V.ι))
  have hr : IsIso ((U.ι ≫ b) ∣_ f ⁻¹ᵁ V) := by
    rw [morphismRestrict_comp]
    have hi : IsIso (U.ι ∣_ b ⁻¹ᵁ (f ⁻¹ᵁ V)) :=
      U.ι.isIso_morphismRestrict_of_le_opensRange (by rwa [Scheme.Opens.opensRange_ι])
    exact IsIso.comp_isIso' hi hb
  have hm : IsIso ((Over.pullback V.ι).map m) := Over.isIso_pullback_map_ι_iff.mpr hr
  intro h
  have hd : IsSchemeTheoreticallyDominant (pullback.fst (Over.mk f).hom V.ι) :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.fst f V.ι))
  have hs : IsSeparated (Over.mk f).hom := inferInstanceAs (IsSeparated f)
  have : IsSplitEpi m := h.isSplitEpi_of_pullback m (inferInstanceAs (Smooth f))
  have hsec : ((section_ m).left ≫ U.ι) ≫ b = 𝟙 X := by
    simpa only [Over.comp_left, Over.id_left, Over.homMk_left, Category.assoc, m, Over.mk_left]
      using congrArg Over.Hom.left (IsSplitEpi.id m)
  have hi : IsSplitEpi I.blowupToBase := IsSplitEpi.mk' ⟨(section_ m).left ≫ U.ι, hsec⟩
  exact hI (Scheme.IdealSheafData.isSplitEpi_blowupToBase_iff.mp hi)

end TauCeti.AlgebraicGeometry.Neron
