/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Basic
public import TauCeti.AlgebraicGeometry.Restrict

/-!
# Composing modifications

Modifications are stable under composition. To find an isomorphism locus for a composite,
shrink an isomorphism locus of the second morphism until its entire preimage lies in an
isomorphism locus of the first. The dense-preimage condition in the definition ensures that
this shrinking remains dense, even for reducible or empty schemes.

The auxiliary results show that a modification pulls back every dense open to a dense open,
and that its isomorphism locus can be shrunk to have preimage in any prescribed dense open.
No integrality, reducedness or Noetherian hypothesis is needed.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory MorphismProperty AlgebraicGeometry TopologicalSpace

namespace TauCeti.AlgebraicGeometry.IsModification

universe u

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y}

/-- The preimage of every dense open under a modification is dense. -/
theorem dense_preimage (hf : IsModification f) {V : Y.Opens} (hV : Dense (V : Set Y)) :
    Dense (f ⁻¹ᵁ V : Set X) := by
  obtain ⟨U, _, hfU, hiso⟩ := hf.exists_isIso_morphismRestrict
  have := Opens.isDominant_ι hfU
  have hd := (hV.preimage U.ι.isOpenEmbedding.isOpenMap).preimage
    (f ∣_ U).isOpenEmbedding.isOpenMap
  refine ((f ⁻¹ᵁ U).ι.denseRange.dense_image (f ⁻¹ᵁ U).ι.continuous hd).mono ?_
  rintro _ ⟨x, hx, rfl⟩
  exact (Scheme.Hom.mem_preimage f).mpr (by
    simpa only [Set.mem_preimage, SetLike.mem_coe, ← Scheme.Hom.comp_apply,
      morphismRestrict_ι] using hx)

/-- A modification has a dense isomorphism locus whose entire preimage lies in any prescribed
dense open of its source. -/
theorem exists_isIso_morphismRestrict_preimage_le (hf : IsModification f)
    {V : X.Opens} (hV : Dense (V : Set X)) :
    ∃ W : Y.Opens, Dense (W : Set Y) ∧ f ⁻¹ᵁ W ≤ V ∧ IsIso (f ∣_ W) := by
  obtain ⟨U, hU, _, hiso⟩ := hf.exists_isIso_morphismRestrict
  have := Opens.isDominant_ι hU
  let T := (f ⁻¹ᵁ U).ι ⁻¹ᵁ V
  let W := U.ι ''ᵁ ((f ∣_ U) ''ᵁ T)
  have hW : Dense (W : Set Y) :=
    U.ι.denseRange.dense_image U.ι.continuous <|
      (f ∣_ U).denseRange.dense_image (f ∣_ U).continuous <|
        hV.preimage (f ⁻¹ᵁ U).ι.isOpenEmbedding.isOpenMap
  have hWU : W ≤ U := by
    rintro _ ⟨y, _, rfl⟩
    exact y.2
  have hpre : f ⁻¹ᵁ W = (f ⁻¹ᵁ U) ⊓ V := by
    dsimp only [W]
    rw [← image_morphismRestrict_preimage, Scheme.Hom.preimage_image_eq,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  refine ⟨W, hW, hpre ▸ inf_le_right, ?_⟩
  exact IsZariskiLocalAtTarget.restrict_of_le (isomorphisms Scheme) hiso hWU

/-- The composite of two modifications is a modification. -/
instance comp (f : X ⟶ Y) (g : Y ⟶ Z) [hf : IsModification f] [hg : IsModification g] :
    IsModification (f ≫ g) where
  exists_isIso_morphismRestrict := by
    obtain ⟨V, hV, _, hfV⟩ := hf.exists_isIso_morphismRestrict
    obtain ⟨W, hW, hWV, hgW⟩ := hg.exists_isIso_morphismRestrict_preimage_le hV
    have hfW : IsIso (f ∣_ g ⁻¹ᵁ W) :=
      IsZariskiLocalAtTarget.restrict_of_le (isomorphisms Scheme) hfV hWV
    refine ⟨W, hW, ?_, ?_⟩
    · simpa only [Scheme.Hom.comp_preimage] using hf.dense_preimage (hg.dense_preimage hW)
    · rw [morphismRestrict_comp]
      exact IsIso.comp_isIso' hfW hgW

/-- The morphism property of being a modification is stable under composition. -/
instance isStableUnderComposition : IsStableUnderComposition @IsModification where
  comp_mem _ _ _ _ := inferInstance

/-- Modifications contain identities and are stable under composition. -/
instance isMultiplicative : IsMultiplicative @IsModification where
  id_mem _ := inferInstance

end TauCeti.AlgebraicGeometry.IsModification
