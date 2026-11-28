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
import TauCeti.CategoryTheory.EpiMono
import TauCeti.CategoryTheory.IrreducibleMorphism

/-!
# An obstruction to the Néron mapping property for blowups

For a separated scheme over a base, the inverse to the projection from the smooth locus of
a blowup over a schematically dense base open cannot extend when the centre is not effective
Cartier. `Scheme.IdealSheafData.smoothLocusBlowupToBase` is the projection in the over category.
`Scheme.IdealSheafData.isIso_pullback_map_smoothLocusBlowupToBase` identifies it as an
isomorphism over the base open where the original scheme is smooth and the blowup is an
isomorphism. `Scheme.IdealSheafData.smoothLocusBlowupToBasePullbackIso` names that isomorphism.
`Scheme.IdealSheafData.smoothLocusBlowupToBasePullbackIso_inv_not_mem_range` gives the
non-extension witness, and `Scheme.IdealSheafData.not_neronMappingProperty_smoothLocus_blowup`
applies it to the Néron mapping property. The obstruction combines Mathlib's smooth locus with
the Cartier criterion `Scheme.IdealSheafData.isSplitEpi_blowupToBase_iff` for blowups.

## References

* S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, §1.2, Definition 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry TauCeti.AlgebraicGeometry.Neron

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {η X S : Scheme.{u}} {f : X ⟶ S} (I : X.IdealSheafData)
  [LocallyOfFinitePresentation (I.blowupToBase ≫ f)]

/-- The projection from the smooth locus of the blowup to the original scheme over `S`. -/
noncomputable def smoothLocusBlowupToBase :
    Over.mk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase ≫ f) ⟶ Over.mk f :=
  Over.homMk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase) (Category.assoc _ _ _)

/-- The underlying scheme map is the smooth-locus inclusion followed by the blowup morphism. -/
@[simp]
theorem smoothLocusBlowupToBase_left :
    (I.smoothLocusBlowupToBase (f := f)).left =
      (I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase := by
  rw [smoothLocusBlowupToBase]
  exact Over.homMk_left _ _

variable (j : η ⟶ S)

/-- The smooth-locus projection is an isomorphism after base change to an open over which
the original scheme is smooth and the blowup morphism is an isomorphism. -/
theorem isIso_pullback_map_smoothLocusBlowupToBase [IsOpenImmersion j]
    (hf : Smooth (f ∣_ j.opensRange))
    (hb : IsIso (I.blowupToBase ∣_ f ⁻¹ᵁ j.opensRange)) :
    IsIso ((Over.pullback j).map (I.smoothLocusBlowupToBase (f := f))) := by
  have hres : Smooth ((I.blowupToBase ≫ f) ∣_ j.opensRange) := by
    rw [morphismRestrict_comp]
    exact inferInstanceAs (Smooth ((I.blowupToBase ∣_ f ⁻¹ᵁ j.opensRange) ≫ (f ∣_ j.opensRange)))
  have hU : I.blowupToBase ⁻¹ᵁ (f ⁻¹ᵁ j.opensRange) ≤ (I.blowupToBase ≫ f).smoothLocus := by
    rw [← Scheme.Hom.comp_preimage]
    apply ((I.blowupToBase ≫ f).smooth_ι_comp_iff_le_smoothLocus _).mp
    rw [← morphismRestrict_ι]
    infer_instance
  rw [Over.Hom.isIso_pullback_map_iff_of_isOpenImmersion, smoothLocusBlowupToBase_left]
  simp only [Over.mk_hom, morphismRestrict_comp]
  have hi : IsIso ((I.blowupToBase ≫ f).smoothLocus.ι ∣_ I.blowupToBase ⁻¹ᵁ (f ⁻¹ᵁ j.opensRange)) :=
    (I.blowupToBase ≫ f).smoothLocus.ι.isIso_morphismRestrict_of_le_opensRange
      (by rwa [Scheme.Opens.opensRange_ι])
  exact IsIso.comp_isIso' hi hb

/-- The isomorphism induced by the smooth-locus projection after base change. -/
noncomputable def smoothLocusBlowupToBasePullbackIso
    [IsIso ((Over.pullback j).map (I.smoothLocusBlowupToBase (f := f)))] :
    (Over.pullback j).obj (Over.mk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase ≫ f)) ≅
      (Over.pullback j).obj (Over.mk f) :=
  asIso ((Over.pullback j).map I.smoothLocusBlowupToBase)

/-- The hom of the base-change isomorphism is the base-changed smooth-locus projection. -/
@[simp]
theorem smoothLocusBlowupToBasePullbackIso_hom
    [IsIso ((Over.pullback j).map (I.smoothLocusBlowupToBase (f := f)))] :
    (I.smoothLocusBlowupToBasePullbackIso (f := f) j).hom =
      (Over.pullback j).map I.smoothLocusBlowupToBase := by
  rw [smoothLocusBlowupToBasePullbackIso, asIso_hom]

/-- Over a schematically dense base change where the smooth-locus projection is an isomorphism,
its inverse cannot extend over the base if the original scheme is separated and the blowup centre
is not effective Cartier. -/
theorem smoothLocusBlowupToBasePullbackIso_inv_not_mem_range [IsSeparated f]
    [IsSchemeTheoreticallyDominant (pullback.fst f j)]
    [IsIso ((Over.pullback j).map (I.smoothLocusBlowupToBase (f := f)))]
    (hI : ¬ I.IsEffectiveCartier) :
    (I.smoothLocusBlowupToBasePullbackIso (f := f) j).inv ∉ Set.range ((Over.pullback j).map :
      (Over.mk f ⟶ Over.mk ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase ≫ f)) → _) := by
  rintro ⟨g, hg⟩
  have hd : IsSchemeTheoreticallyDominant (pullback.fst (Over.mk f).hom j) := by
    simpa only [Over.mk_hom] using
      (inferInstance : IsSchemeTheoreticallyDominant (pullback.fst f j))
  have hs : IsSeparated (Over.mk f).hom := by
    simpa only [Over.mk_hom] using (inferInstance : IsSeparated f)
  have hm : IsSplitEpi (I.smoothLocusBlowupToBase (f := f)) := by
    refine (Over.pullback j).isSplitEpi_of_map_comp_eq_id (g := g)
      (Over.pullback_map_injective_of_isSchemeTheoreticallyDominant j) ?_
    rw [hg, ← smoothLocusBlowupToBasePullbackIso_hom, Iso.inv_hom_id]
  have hc : IsSplitEpi ((I.blowupToBase ≫ f).smoothLocus.ι ≫ I.blowupToBase) := by
    simpa only [Over.forget_map, smoothLocusBlowupToBase_left] using
      (inferInstance : IsSplitEpi ((Over.forget S).map (I.smoothLocusBlowupToBase (f := f))))
  exact hI (I.isSplitEpi_blowupToBase_iff.mp
    (TauCeti.isSplitEpi_of_isSplitEpi_comp (I.blowupToBase ≫ f).smoothLocus.ι I.blowupToBase))

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
  have hi := I.isIso_pullback_map_smoothLocusBlowupToBase j
    (inferInstance : Smooth (f ∣_ j.opensRange)) hb
  exact MappingProperty.not_of_not_surjective (Over.mk f) hs fun h ↦
    I.smoothLocusBlowupToBasePullbackIso_inv_not_mem_range (f := f) j hI (h _)

end AlgebraicGeometry.Scheme.IdealSheafData
