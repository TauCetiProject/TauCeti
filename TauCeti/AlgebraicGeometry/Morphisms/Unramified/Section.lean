/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.AlgebraicGeometry.Morphisms.Unramified.Basic
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import TauCeti.AlgebraicGeometry.IdealSheaf.Section
import TauCeti.AlgebraicGeometry.Morphisms.LocallyQuasiFinite

/-!
# Images of sections of unramified morphisms

A section of an unramified morphism is an open immersion. For a separated unramified
morphism, taking its image identifies sections with clopen subschemes mapping isomorphically
to the base (`AlgebraicGeometry.Scheme.Hom.splitEpiEquivClopens`). The inverse sends such a
subscheme to the inverse of its structure map followed by its inclusion.

Let `f : X ⟶ Y` be an unramified morphism with geometrically connected fibres. Every section
`s : Y ⟶ X` of `f` is an isomorphism
(`TauCeti.AlgebraicGeometry.isIso_of_comp_eq_id_of_unramified`), and hence so is `f`. Indeed `s`
is an open immersion, since `s ≫ f = 𝟙 Y` is one and open immersions cancel against unramified
morphisms on the right. The fibres of `f` are discrete, since `f` is locally quasi-finite, and
connected, so each of them is the single point it shares with the image of `s`; thus `s` is
surjective.

## References

* The Stacks Project, [Tag 024T](https://stacks.math.columbia.edu/tag/024T).
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry TopologicalSpace

variable {X S : Scheme.{u}}

/-- A section of an unramified morphism is an open immersion. -/
theorem isOpenImmersion_of_comp_eq_id (s : S ⟶ X) {f : X ⟶ S} [Unramified f]
    (hs : s ≫ f = 𝟙 S) : IsOpenImmersion s :=
  have : IsOpenImmersion (s ≫ f) := hs ▸ inferInstance
  MorphismProperty.of_postcomp (W' := @Unramified) _ _ f ‹_› this

/-- The open image of an open-immersion section maps isomorphically to the base. -/
theorem isIso_opensRange_ι_comp_of_comp_eq_id (s : S ⟶ X) [IsOpenImmersion s]
    {f : X ⟶ S} (hs : s ≫ f = 𝟙 S) : IsIso (s.opensRange.ι ≫ f) := by
  rw [← s.isoOpensRange_inv_comp, Category.assoc, hs, Category.comp_id]
  infer_instance

/-- Sections of a separated unramified morphism correspond to the open and closed
subschemes of its source that map isomorphically to its target. -/
noncomputable def splitEpiEquivClopens (f : X ⟶ S) [Unramified f] [IsSeparated f] :
    SplitEpi f ≃ {U : Clopens X // IsIso (Scheme.Opens.ι U.toOpens ≫ f)} where
  toFun s :=
    have := s.section_.isOpenImmersion_of_comp_eq_id s.id
    have := s.section_.isClosedImmersion_of_comp_eq_id s.id
    ⟨⟨Set.range s.section_, s.section_.isClosedMap.isClosed_range,
      s.section_.isOpenEmbedding.isOpen_range⟩,
      s.section_.isIso_opensRange_ι_comp_of_comp_eq_id s.id⟩
  invFun U :=
    have := U.property
    ⟨inv (Scheme.Opens.ι U.val.toOpens ≫ f) ≫ Scheme.Opens.ι U.val.toOpens, by simp⟩
  left_inv s := by
    have := s.section_.isOpenImmersion_of_comp_eq_id s.id
    have := s.section_.isIso_opensRange_ι_comp_of_comp_eq_id s.id
    have hinv : inv (s.section_.opensRange.ι ≫ f) = s.section_.isoOpensRange.hom :=
      IsIso.inv_eq_of_inv_hom_id (by simp)
    exact SplitEpi.ext ((congrArg (· ≫ s.section_.opensRange.ι) hinv).trans
      s.section_.isoOpensRange_hom_ι)
  right_inv U := by
    have := U.property
    apply Subtype.ext
    apply SetLike.coe_injective
    exact ((inv (Scheme.Opens.ι U.val.toOpens ≫ f)).surjective.range_comp
      (Scheme.Opens.ι U.val.toOpens)).trans (Scheme.Opens.range_ι _)

/-- The underlying set of the clopen subscheme attached to a section is its image. -/
@[simp]
theorem coe_splitEpiEquivClopens_apply (f : X ⟶ S) [Unramified f] [IsSeparated f]
    (s : SplitEpi f) : ((f.splitEpiEquivClopens s).val : Set X) = Set.range s.section_ :=
  (rfl)

/-- Recover the section by inverting the structure map on the clopen subscheme. -/
@[simp]
theorem splitEpiEquivClopens_symm_apply_section_ (f : X ⟶ S) [Unramified f] [IsSeparated f]
    (U : {U : Clopens X // IsIso (Scheme.Opens.ι U.toOpens ≫ f)}) :
    letI := U.property
    (f.splitEpiEquivClopens.symm U).section_ =
      inv (Scheme.Opens.ι U.val.toOpens ≫ f) ≫ Scheme.Opens.ι U.val.toOpens :=
  (rfl)

end AlgebraicGeometry.Scheme.Hom

namespace TauCeti.AlgebraicGeometry

/-- **A section of an unramified morphism with geometrically connected fibres is an
isomorphism.** -/
theorem isIso_of_comp_eq_id_of_unramified {X Y : Scheme.{u}} (f : X ⟶ Y) [Unramified f]
    [GeometricallyConnected f] (s : Y ⟶ X) (hs : s ≫ f = 𝟙 Y) : IsIso s := by
  have := s.isOpenImmersion_of_comp_eq_id hs
  refine (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨this, ⟨fun x ↦ ?_⟩⟩
  -- The fibre through `x` is discrete and connected, so it is the point `s (f x)`.
  have hsub : (f ⁻¹' {f x}).Subsingleton :=
    (f.isConnected_preimage_singleton _).isPreconnected.isDiscrete_iff_subsingleton.mp
      (f.isDiscrete_preimage_singleton _)
  refine ⟨f x, hsub ?_ (Set.mem_preimage.2 (Set.mem_singleton _))⟩
  rw [Set.mem_preimage, Set.mem_singleton_iff, ← Scheme.Hom.comp_apply, hs]
  simp

end TauCeti.AlgebraicGeometry
