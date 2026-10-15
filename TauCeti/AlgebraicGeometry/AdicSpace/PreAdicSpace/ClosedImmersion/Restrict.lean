/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.ClosedImmersion.Local

import TauCeti.RingTheory.Huber.LocalizationTopology.IdealQuotient

/-!
# Restricting closed immersions over opens of the target

A closed immersion `f : X ⟶ Y` of pre-adic spaces (`TauCeti.PreAdicSpace.IsClosedImmersion`) is
defined by asking for a closed quotient model `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)` over *some* open
neighbourhood of each point of `Y`. This file shows that, when the structure presheaf of `Y` is a
sheaf, closed immersions restrict to closed immersions over every open of `Y`. So being a closed
immersion is local on the target, and it does not depend on the charts used to verify it.

The local input is the restriction of the quotient morphism over a rational subset `R(T/s)` of
`Spa(A, A⁺)`. By Wedhorn's Remark 8.8, `R(T/s)` is `Spa(A⟨T/s⟩, A_U⁺)` and its preimage is
`Spa((A ⧸ J)⟨q(T)/q(s)⟩, (A ⧸ J)_U⁺)`, where `q : A → A ⧸ J` is the quotient map. Under these
identifications the restricted morphism is induced by the quotient mapping
`A⟨T/s⟩ → (A ⧸ J)⟨q(T)/q(s)⟩`
(`TauCeti.Huber.PairOfDefinition.isQuotientMapping_completionLocQuotientPairHom`), whose kernel is
the closure of `J · A⟨T/s⟩`, and a morphism induced by a quotient mapping with closed kernel is a
closed immersion (`isClosedImmersion_presentationLimitPreAdicSpaceComap_of_isQuotientMapping`).
Rational subsets form a basis of the topology, and closed immersions descend along open covers of
the target (`TauCeti.PreAdicSpace.IsClosedImmersion.of_iSup_eq_top`), which gives the general case.

The sheaf condition on the target is used for the morphism `Spa(A⟨T/s⟩, A_U⁺) ⟶ Spa(A, A⁺)` induced
by the structure map, which needs the structure presheaf of its source to be a sheaf.

## Main results

* `isClosedImmersion_restrictPreimage_presentationLimitPreAdicSpaceQuotientComap`: over a
  sheafy `Spa(A, A⁺)`, the quotient morphism restricted over a rational subset is a closed
  immersion.
* `TauCeti.PreAdicSpace.IsClosedImmersion.restrictPreimage`: a closed immersion into a sheafy
  pre-adic space restricts to a closed immersion over every open of the target.
* `TauCeti.PreAdicSpace.isClosedImmersion_iff_of_iSup_eq_top`: over a sheafy target, a morphism is
  a closed immersion exactly when its restrictions over the members of an open cover are.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definition 7.22, Proposition 7.38, Remark 8.8
  and §8.3.
-/

public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber Huber.PairOfDefinition

universe u

namespace ValuationSpectrum

open PreAdicSpace

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
  (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) (J : Ideal A)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa (S.quotient J).plus))
    (presentationLimitPresheaf (P.quotient J) (S.quotient J).plus))

/-- **The quotient morphism restricts to a closed immersion over a rational subset.** Let
`(A, A⁺)` be a Huber pair whose structure presheaf is a sheaf, `J ⊆ A` an ideal with sheafy
quotient pair, and `R(T/s)` a rational subset of `Spa(A, A⁺)` with `T` spanning an open ideal.
Then the quotient morphism `Spa(A ⧸ J, (A ⧸ J)⁺) ⟶ Spa(A, A⁺)`, restricted over `R(T/s)`, is a
closed immersion. The ideal `J` need not be closed: over `R(T/s) ≅ Spa(A⟨T/s⟩, A_U⁺)` the closed
ideal of the quotient model is the closure of `J · A⟨T/s⟩` in `A⟨T/s⟩`. -/
theorem isClosedImmersion_restrictPreimage_presentationLimitPreAdicSpaceQuotientComap
    {T : Finset A} {s : A} (hT : IsOpen (Ideal.span (T : Set A) : Set A))
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus)) :
    IsClosedImmersion ((presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf).restrictPreimage
      (spaBasicOpen S.plus T s)) := by
  -- The square of pre-adic spaces induced by the square of Huber pairs
  --   `A → A⟨T/s⟩`, `A ⧸ J → (A ⧸ J)⟨q(T)/q(s)⟩`, `A → A ⧸ J`, `A⟨T/s⟩ → (A ⧸ J)⟨q(T)/q(s)⟩`
  -- has open immersions onto `R(T/s)` and onto its preimage as vertical sides, and the morphism
  -- induced by the quotient mapping as its top side, which is a closed immersion.
  classical
  let L := Localization.Away s
  let L' := Localization.Away (Ideal.Quotient.mk J s)
  let T' : Finset (A ⧸ J) := T.image (Ideal.Quotient.mk J)
  have hT' : (T' : Set (A ⧸ J)) = Ideal.Quotient.mk J '' T := Finset.coe_image
  have hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  have hden' := P.hasDenominatorPower_quotient J T s L hT' L' hden
  let _ := P.locUniformSpace T s L hden
  have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  let _ := (P.quotient J).locUniformSpace T' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isUniformAddGroup_locUniformSpace T' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isTopologicalRing_locUniformSpace T' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isHuberRing_completion_locTopology T' (Ideal.Quotient.mk J s) L' hden'
  have hTq : IsOpen (Ideal.span (T' : Set (A ⧸ J)) : Set (A ⧸ J)) := by
    rw [hT', ← Ideal.map_span, Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
    exact (QuotientRing.isOpenQuotientMap_mk J).isOpenMap _ hT
  have hPq := P.quotient_ringOfDefinition_le_quotient_plus hP J
  let Sloc := P.rationalLocalizationPair S hP T s L hden
  let Sloc' := (P.quotient J).rationalLocalizationPair (S.quotient J) hPq T'
    (Ideal.Quotient.mk J s) L' hden'
  let Ploc := P.completionLocalization T s L hden
  let Ploc' := (P.quotient J).completionLocalization T' (Ideal.Quotient.mk J s) L' hden'
  have hPloc : Ploc.ringOfDefinition ≤ Sloc.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP T s L hden
  have hPloc' : Ploc'.ringOfDefinition ≤ Sloc'.plus := by
    rw [rationalLocalizationPair_plus]
    exact (P.quotient J).completionLocalization_ringOfDefinition_le_completedPlusSubring
      (S.quotient J).plus hPq T' (Ideal.Quotient.mk J s) L' hden'
  -- the structure presheaves of both rational localisations are sheaves
  have hsY : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Sloc.plus))
      (presentationLimitPresheaf Ploc Sloc.plus) := by
    rw [rationalLocalizationPair_plus]
    exact isSheaf_presentationLimitPresheaf_completionLocalization P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP T s L hden hT hsheafA
  have hsX : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa Sloc'.plus))
      (presentationLimitPresheaf Ploc' Sloc'.plus) := by
    rw [rationalLocalizationPair_plus]
    exact isSheaf_presentationLimitPresheaf_completionLocalization (P.quotient J)
      (S.quotient J).plus (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem hPq T'
      (Ideal.Quotient.mk J s) L' hden' hTq hsheaf
  -- the top side: the quotient mapping `π : A⟨T/s⟩ → (A ⧸ J)⟨q(T)/q(s)⟩`, with closed kernel
  let π := P.completionLocQuotientPairHom J T s L hT' L' S hP hden
  have hπ : π.IsQuotientMapping :=
    P.isQuotientMapping_completionLocQuotientPairHom J T s L hT' L' S hP hden
  have hK : IsClosed (RingHom.ker π.toRingHom : Set (UniformSpace.Completion L)) :=
    isClosed_singleton.preimage π.continuous_toRingHom
  -- the vertical sides: the open immersions induced by the structure maps
  let v := presentationLimitPreAdicSpaceComap (P' := Ploc)
    (P.toCompletionLocHom S hP T s L hden).toRingHom
    (P.toCompletionLocHom S hP T s L hden).continuous_toRingHom
    (fun _ hI ↦ by
      rw [toRingHom_toCompletionLocHom]
      exact P.isOpen_map_toCompletionLoc T s L hden hI)
    (P.toCompletionLocHom S hP T s L hden).map_mem_plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    Sloc.isRingOfIntegralElements.isPowerBounded_of_mem hP hPloc hsY
  have hvo : IsOpenImmersion v :=
    isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP T s L hden hT hsY
  have hvr : Set.range v.base = (spaBasicOpen S.plus T s : Set (spa S.plus)) :=
    range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P hP T s L hden hsY
  let u := presentationLimitPreAdicSpaceComap (P' := Ploc')
    ((P.quotient J).toCompletionLocHom (S.quotient J) hPq T' (Ideal.Quotient.mk J s) L'
      hden').toRingHom
    ((P.quotient J).toCompletionLocHom (S.quotient J) hPq T' (Ideal.Quotient.mk J s) L'
      hden').continuous_toRingHom
    (fun _ hI ↦ by
      rw [toRingHom_toCompletionLocHom]
      exact (P.quotient J).isOpen_map_toCompletionLoc T' (Ideal.Quotient.mk J s) L' hden' hI)
    ((P.quotient J).toCompletionLocHom (S.quotient J) hPq T' (Ideal.Quotient.mk J s) L'
      hden').map_mem_plus
    (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
    Sloc'.isRingOfIntegralElements.isPowerBounded_of_mem hPq hPloc' hsX
  have huo : IsOpenImmersion u :=
    isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom (P.quotient J) hPq T'
      (Ideal.Quotient.mk J s) L' hden' hTq hsX
  have hur : Set.range u.base = (spaBasicOpen (S.quotient J).plus T' (Ideal.Quotient.mk J s) :
      Set (spa (S.quotient J).plus)) :=
    range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base (P.quotient J) hPq T'
      (Ideal.Quotient.mk J s) L' hden' hsX
  refine (Hom.prop_restrictPreimage_iff_of_isOpenImmersion _ (spaBasicOpen S.plus T s)
    (@IsClosedImmersion.{u}) _ u v hvr ?_ ?_).mpr
    (isClosedImmersion_presentationLimitPreAdicSpaceComap_of_isQuotientMapping Sloc Ploc hPloc
      Ploc' hPloc' π hπ hK hsX)
  · -- the preimage of `R(T/s)` under the quotient morphism is `R(q(T)/q(s))`
    rw [hur, coe_presentationLimitPreAdicSpaceQuotientComap_base]
    ext x
    have := Set.ext_iff.mp (Pair.Hom.spaComap_preimage_rationalSubset (Pair.quotientHom S J) T s) x
    simp only [Pair.Hom.toRingHom_quotientHom, Set.mem_preimage] at this
    rw [SetLike.mem_coe, mem_spaBasicOpen]
    exact this.symm.trans mem_spaBasicOpen.symm
  · -- the square commutes, since `π` is compatible with the structure maps
    rw [presentationLimitPreAdicSpaceQuotientComap_def]
    simp only [u, v]
    rw [← presentationLimitPreAdicSpaceComap_comp, ← presentationLimitPreAdicSpaceComap_comp]
    congr 1
    rw [toRingHom_completionLocQuotientPairHom, toRingHom_toCompletionLocHom,
      toRingHom_toCompletionLocHom]
    exact P.completionLocQuotientHom_comp_toCompletionLoc J T s L hT' L' hden

end ValuationSpectrum

namespace PreAdicSpace

open ValuationSpectrum

variable {X Y : PreAdicSpace.{u}}

-- Every point `y` of an open `W` of the target has an open neighbourhood `V' ≤ W` over which a
-- closed immersion into a sheafy pre-adic space restricts to a closed immersion: `V'` is the image
-- of a rational subset `R(T/s)` of an affinoid chart `Spa(A, A⁺)` at `y`, and over it the closed
-- immersion is the restriction of the quotient morphism `Spa(A ⧸ J) ⟶ Spa(A)` to `R(T/s)`.
private theorem IsClosedImmersion.exists_le_isClosedImmersion_restrictPreimage {f : X ⟶ Y}
    (hf : IsClosedImmersion f) (hY : isSheafy Y) (W : Opens Y) (y : W) :
    ∃ V' : Opens Y, y.1 ∈ V' ∧ V' ≤ W ∧ IsClosedImmersion (f.restrictPreimage V') := by
  obtain ⟨V, hyV, A, _, _, _, _, S, P, hP, J, -, hsheaf, eV, eU, hfac⟩ :=
    (isClosedImmersion_iff f).mp hf y.1
  have hsA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ hY)
  -- a rational open `R(T/s)` of `Spa(A, A⁺)` around the image of `y`, inside the image of `W`
  let O' : Opens (spa S.plus) := (Opens.map eV.inv.base).obj
    ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W)
  have hinv : eV.inv.base (eV.hom.base ⟨y.1, hyV⟩) = ⟨y.1, hyV⟩ :=
    congrArg (fun g ↦ g.base ⟨y.1, hyV⟩) eV.hom_inv_id
  have hz : eV.hom.base ⟨y.1, hyV⟩ ∈ O' := by
    refine Opens.mem_map.mpr (Opens.mem_map.mpr ?_)
    have h : (Y.ofRestrict V.isOpenEmbedding).base (eV.inv.base (eV.hom.base ⟨y.1, hyV⟩)) =
        y.1 := by
      rw [hinv]
      rfl
    exact Eq.mpr (congrArg (· ∈ W) h) y.2
  obtain ⟨R, hR, hzR, hRO⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens S.plus) hz
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hR
  -- over the image `V'` of `R(T/s)` in `Y`, `f` is the quotient morphism restricted to `R(T/s)`
  let q := presentationLimitPreAdicSpaceQuotientComap S P hP J hsheaf
  let R : Opens (presentationLimitPreAdicSpace P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP) := spaBasicOpen S.plus T s
  let v := (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP).ofRestrict R.isOpenEmbedding ≫
    eV.inv ≫ Y.ofRestrict V.isOpenEmbedding
  let u := (presentationLimitPreAdicSpace (P.quotient J) (S.quotient J).plus
      (S.quotient J).isRingOfIntegralElements.isPowerBounded_of_mem
      (P.quotient_ringOfDefinition_le_quotient_plus hP J)).ofRestrict
      ((Opens.map q.base).obj R).isOpenEmbedding ≫
    eU.inv ≫ X.ofRestrict ((Opens.map f.base).obj V).isOpenEmbedding
  let V' : Opens Y := ⟨Set.range v.base, v.isOpenEmbedding.isOpen_range⟩
  have w : q.restrictPreimage R ≫ v = u ≫ f := by
    simp only [v, u, Category.assoc, Hom.restrictPreimage_ofRestrict_assoc, hfac,
      Iso.inv_hom_id_assoc, q]
  have : IsOpenImmersion eV.inv := @IsOpenImmersion.of_isIso _ _ eV.inv eV.isIso_inv
  have hinj := (eV.inv ≫ Y.ofRestrict V.isOpenEmbedding).isOpenEmbedding.injective
  have hu : Set.range u.base = f.base ⁻¹' (V' : Set Y) := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨(q.restrictPreimage R).base z, congrArg (fun g ↦ g.base z) w⟩
    · rintro ⟨r, hr⟩
      -- `f x` lies in `V`; the point of `Spa(A ⧸ J)` over `x` maps to the point `r` of `R(T/s)`
      have hxV : f.base x ∈ V := Eq.mpr (congrArg (· ∈ V) hr.symm) (eV.inv.base r.1).2
      let x' : X.restrict ((Opens.map f.base).obj V).isOpenEmbedding :=
        ⟨x, Opens.mem_map.mpr hxV⟩
      have hfx : (eV.inv ≫ Y.ofRestrict V.isOpenEmbedding).base (q.base (eU.hom.base x')) =
          (eV.inv ≫ Y.ofRestrict V.isOpenEmbedding).base r.1 :=
        (congrArg (fun g ↦ g.base x') hfac).symm.trans hr.symm
      have hzR : eU.hom.base x' ∈ (Opens.map q.base).obj R :=
        Opens.mem_map.mpr (Eq.mpr (congrArg (· ∈ R) (hinj hfx)) r.2)
      exact ⟨⟨eU.hom.base x', hzR⟩, congrArg (fun g ↦ (g.base x').1) eU.hom_inv_id⟩
  have hV' : IsClosedImmersion (f.restrictPreimage V') :=
    (Hom.prop_restrictPreimage_iff_of_isOpenImmersion f V' (@IsClosedImmersion.{u})
      (q.restrictPreimage R) u v rfl hu w).mpr
      (isClosedImmersion_restrictPreimage_presentationLimitPreAdicSpaceQuotientComap S P hP J
        hsheaf hT hsA)
  have hV'W : (V' : Set Y) ⊆ W := by
    rintro _ ⟨r, rfl⟩
    exact Opens.mem_map.mp (Opens.mem_map.mp (hRO r.2))
  exact ⟨V', ⟨⟨eV.hom.base ⟨y.1, hyV⟩, hzR⟩, congrArg Subtype.val hinv⟩, hV'W, hV'⟩

/-- **A closed immersion restricts to a closed immersion over every open of the target**, when the
target is sheafy: if `f : X ⟶ Y` is a closed immersion and the structure presheaf of `Y` is a
sheaf, then `f⁻¹(W) → W` is a closed immersion for every open `W` of `Y`. So the closed quotient
models of `f` exist over every open of `Y`, not only over the neighbourhoods chosen in the
definition. -/
theorem IsClosedImmersion.restrictPreimage {f : X ⟶ Y} (hf : IsClosedImmersion f)
    (hY : isSheafy Y) (W : Opens Y) : IsClosedImmersion (f.restrictPreimage W) :=
  Hom.prop_restrictPreimage_of_forall_exists_le f (@IsClosedImmersion.{u})
    (fun _ ↦ IsClosedImmersion.of_iSup_eq_top) W
    (hf.exists_le_isClosedImmersion_restrictPreimage hY W)

/-- **Being a closed immersion is local on a sheafy target**: for a morphism `f : X ⟶ Y` into a
pre-adic space with sheaf structure presheaf and an open cover `V` of `Y`, `f` is a closed immersion
exactly when each restriction `f⁻¹(V i) → V i` is. In particular the condition does not depend on
the cover, or on the affinoid charts, used to verify it. -/
theorem isClosedImmersion_iff_of_iSup_eq_top {f : X ⟶ Y} (hY : isSheafy Y) {ι : Type*}
    (V : ι → Opens Y) (hV : iSup V = ⊤) :
    IsClosedImmersion f ↔ ∀ i, IsClosedImmersion (f.restrictPreimage (V i)) :=
  ⟨fun hf i ↦ hf.restrictPreimage hY (V i), IsClosedImmersion.of_iSup_eq_top V hV⟩

end PreAdicSpace

end TauCeti

end
