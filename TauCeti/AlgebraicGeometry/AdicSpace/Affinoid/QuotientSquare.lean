/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid.Basic

import TauCeti.RingTheory.Huber.LocalizationTopology.IdealQuotient
import TauCeti.Topology.Algebra.Ring.Ideal

/-!
# Rational-localization pullback squares for ideal quotients of affinoid adic spaces

Given a sheafy Huber pair `(A, S)` and an ideal `J : Ideal A` such that `(A ⧸ J, (S.quotient J)⁺)`
is also sheafy, this file constructs local pullback squares over rational opens of
`AdicSpace.ofPair S hS` modelling the closed-subspace morphism
`ofPair (S.quotient J) hSJ ⟶ ofPair S hS` by an ideal quotient of a complete Hausdorff sheafy Huber
pair.

Keeping these `Type`-valued square structures in a downstream module allows `AdicSpace.ofPair` to
remain unexposed (`@[expose]`-free) in `TauCeti.AlgebraicGeometry.AdicSpace.Affinoid.Basic`.

## Main definitions

* `TauCeti.AdicSpace.OfPairQuotientOpenSquare`: data of a local pullback square over a specified
  open `O` of `ofPair S hS` modelling `S.quotient J` via an ideal `ideal` preserving nilpotency
  exponents of `J`.
* `TauCeti.AdicSpace.OfPairQuotientRationalSquare`: a neighbourhood `openSet ≤ W` around a point
  `z ∈ W` together with an `OfPairQuotientOpenSquare` over `openSet`.

## Main results

* `TauCeti.AdicSpace.exists_ofPair_quotient_open_square`: constructs an `OfPairQuotientOpenSquare`
  for fixed rational data `(F, s, hF)`.
* `TauCeti.AdicSpace.exists_ofPair_quotient_rational_square`: around any point `z` in an open
  `W` of `ofPair S hS`, produces an open neighbourhood `openSet ≤ W` of `z` carrying an
  `OfPairQuotientOpenSquare`.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti.AdicSpace

open Huber PreAdicSpace ValuationSpectrum

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]

private theorem quotientKer_of_isQuotientMapping
    {A₁ : Type u} [CommRing A₁] [TopologicalSpace A₁] [IsTopologicalRing A₁] [IsHuberRing A₁]
    {A₂ : Type u} [CommRing A₂] [UniformSpace A₂] [IsUniformAddGroup A₂] [IsTopologicalRing A₂]
    [CompleteSpace A₂] [T2Space A₂] [IsHuberRing A₂] {S₁ : Pair A₁} {S₂ : Pair A₂}
    {π : Pair.Hom S₁ S₂} (hq : π.IsQuotientMapping) (hS₂ : IsSheafyForEveryPresentation S₂.plus) :
    ∃ (hSK : IsSheafyForEveryPresentation (S₁.quotient (RingHom.ker π.toRingHom)).plus)
      (eSK : ofPair (S₁.quotient (RingHom.ker π.toRingHom)) hSK ≅ ofPair S₂ hS₂),
      T2Space (A₁ ⧸ RingHom.ker π.toRingHom) ∧
      @CompleteSpace (A₁ ⧸ RingHom.ker π.toRingHom)
        (IsTopologicalAddGroup.rightUniformSpace (A₁ ⧸ RingHom.ker π.toRingHom)) ∧
      eSK.hom = comapOfPair hS₂ hSK hq.quotientKerInverse := by
  let K := RingHom.ker π.toRingHom
  let φ := Pair.Hom.quotientLift K π le_rfl
  let ψ := hq.quotientKerInverse
  let e : (A₁ ⧸ K) ≃+* A₂ :=
    { φ.toRingHom with
      invFun := ψ.toRingHom
      left_inv := hq.quotientKerInverse_toRingHom_quotientLift
      right_inv := hq.quotientLift_toRingHom_quotientKerInverse }
  let _ : UniformSpace (A₁ ⧸ K) := IsTopologicalAddGroup.rightUniformSpace (A₁ ⧸ K)
  have _ : IsUniformAddGroup (A₁ ⧸ K) := isUniformAddGroup_of_addCommGroup
  let ue : (A₁ ⧸ K) ≃ᵤ A₂ :=
    ⟨e.toEquiv, uniformContinuous_addMonoidHom_of_continuous φ.continuous_toRingHom,
      uniformContinuous_addMonoidHom_of_continuous ψ.continuous_toRingHom⟩
  have hplus : (S₁.quotient K).plus.map (e : _ →+* _) = S₂.plus := Subring.ext fun b ↦
    ⟨by rintro ⟨x, hx, rfl⟩; exact φ.map_mem_plus x hx,
      fun hb ↦ ⟨ψ.toRingHom b, ψ.map_mem_plus b hb,
        hq.quotientLift_toRingHom_quotientKerInverse b⟩⟩
  have hSK := (isSheafyForEveryPresentation_iff_of_ringEquiv e φ.continuous_toRingHom
    ψ.continuous_toRingHom hplus).mpr hS₂
  refine ⟨hSK,
    { hom := comapOfPair hS₂ hSK ψ, inv := comapOfPair hSK hS₂ φ
      hom_inv_id := by
        rw [← comapOfPair_comp, hq.quotientKerInverse_comp_quotientLift, comapOfPair_id]
      inv_hom_id := by
        rw [← comapOfPair_comp, hq.quotientLift_comp_quotientKerInverse, comapOfPair_id] },
    ue.symm.toHomeomorph.t2Space, ue.completeSpace_iff.mpr inferInstance, rfl⟩

/-- **Pullback square over a specified open** `O` of `ofPair S hS` for an ideal quotient
`S.quotient J`: a complete Hausdorff sheafy Huber pair `pair`, an ideal `ideal` preserving any
nilpotency exponent of `J`, open immersions `targetMap` onto `O` and `quotientMap` onto the
preimage of `O` in `ofPair (S.quotient J) hSJ`, and the commutative pullback square. -/
structure OfPairQuotientOpenSquare {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] (S : Pair A)
    (hS : IsSheafyForEveryPresentation S.plus) (J : Ideal A)
    (hSJ : IsSheafyForEveryPresentation (S.quotient J).plus)
    (O : Opens (ofPair S hS).obj) where
  /-- The coefficient ring of the local chart modelling `O`. -/
  Ring : Type u
  [commRing : CommRing Ring]
  [uniformSpace : UniformSpace Ring]
  [isUniformAddGroup : IsUniformAddGroup Ring]
  [isTopologicalRing : IsTopologicalRing Ring]
  [completeSpace : CompleteSpace Ring]
  [t2Space : T2Space Ring]
  [isHuberRing : IsHuberRing Ring]
  /-- The sheafy Huber pair on `Ring`. -/
  pair : Pair Ring
  /-- Sheafiness of `pair`. -/
  isSheafy : IsSheafyForEveryPresentation pair.plus
  /-- An ideal of `Ring` whose quotient pair models the restriction of `S.quotient J` over `O`. -/
  ideal : Ideal Ring
  /-- Sheafiness of the quotient pair `pair.quotient ideal`. -/
  isSheafyQuotient : IsSheafyForEveryPresentation (pair.quotient ideal).plus
  [t2SpaceQuotient : T2Space (Ring ⧸ ideal)]
  /-- Completeness of `Ring ⧸ ideal` for its canonical right uniformity. -/
  completeSpaceQuotient : @CompleteSpace (Ring ⧸ ideal)
    (IsTopologicalAddGroup.rightUniformSpace (Ring ⧸ ideal))
  /-- Preservation of any nilpotency exponent of `J` on `ideal`. -/
  pow_eq_bot : ∀ {n : ℕ}, J ^ n = ⊥ → ideal ^ n = ⊥
  /-- The open immersion `Spa(Ring, pair⁺) ⟶ Spa(A, S⁺)` onto `O`. -/
  targetMap : ofPair pair isSheafy ⟶ ofPair S hS
  /-- The open immersion `Spa(Ring ⧸ ideal, ...) ⟶ Spa(A ⧸ J, ...)` onto the preimage of `O`. -/
  quotientMap : ofPair (pair.quotient ideal) isSheafyQuotient ⟶ ofPair (S.quotient J) hSJ
  [isOpenImmersion_targetMap : PreAdicSpace.IsOpenImmersion targetMap.hom]
  /-- The image of `targetMap` is `O`. -/
  range_targetMap : Set.range targetMap.hom.base = (O : Set (ofPair S hS).obj)
  [isOpenImmersion_quotientMap : PreAdicSpace.IsOpenImmersion quotientMap.hom]
  /-- The image of `quotientMap` is the preimage of `O` in `Spa(A ⧸ J, ...)`. -/
  range_quotientMap : Set.range quotientMap.hom.base =
    (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base ⁻¹' (O : Set (ofPair S hS).obj)
  /-- Commutativity of the pullback square. -/
  comm : comapOfPair isSheafy isSheafyQuotient (Pair.quotientHom pair ideal) ≫ targetMap =
    quotientMap ≫ comapOfPair hS hSJ (Pair.quotientHom S J)

attribute [instance] OfPairQuotientOpenSquare.commRing
  OfPairQuotientOpenSquare.uniformSpace OfPairQuotientOpenSquare.isUniformAddGroup
  OfPairQuotientOpenSquare.isTopologicalRing OfPairQuotientOpenSquare.completeSpace
  OfPairQuotientOpenSquare.t2Space OfPairQuotientOpenSquare.isHuberRing
  OfPairQuotientOpenSquare.t2SpaceQuotient
  OfPairQuotientOpenSquare.isOpenImmersion_targetMap
  OfPairQuotientOpenSquare.isOpenImmersion_quotientMap

/-- **Existence of an `OfPairQuotientOpenSquare` over a rational open.** For rational data
`(F, s, hF)` of a sheafy Huber pair `(A, S)` and an ideal `J : Ideal A` with sheafy quotient
`S.quotient J`, there exists an `OfPairQuotientOpenSquare` over the rational open
`ofPairHomeomorph S hS ⁻¹' spaBasicOpen S.plus F s`. -/
theorem exists_ofPair_quotient_open_square (S : Pair A)
    (hS : IsSheafyForEveryPresentation S.plus) (J : Ideal A)
    (hSJ : IsSheafyForEveryPresentation (S.quotient J).plus)
    (F : Finset A) (s : A) (hF : IsOpen (Ideal.span (F : Set A) : Set A)) :
    Nonempty (OfPairQuotientOpenSquare S hS J hSJ
      ⟨ofPairHomeomorph S hS ⁻¹' (spaBasicOpen S.plus F s : Set (spa S.plus)),
        (spaBasicOpen S.plus F s).isOpen.preimage (ofPairHomeomorph S hS).continuous⟩) := by
  classical
  -- Take `Ring` to be the completed rational localization of `A` at `(F, s)` and `ideal` to be
  -- the kernel of the quotient mapping to the corresponding completed rational localization of
  -- `A ⧸ J` (the closure of the extension of `J`).
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  let O : Opens (ofPair S hS).obj :=
    ⟨ofPairHomeomorph S hS ⁻¹' (spaBasicOpen S.plus F s : Set (spa S.plus)),
      (spaBasicOpen S.plus F s).isOpen.preimage (ofPairHomeomorph S hS).continuous⟩
  -- Form the rational localizations `S₁` of `S` and `S₂` of `S.quotient J`
  have hPq := P.quotient_ringOfDefinition_le_quotient_plus hP J
  let L := Localization.Away s
  let L' := Localization.Away (Ideal.Quotient.mk J s)
  let F' : Finset (A ⧸ J) := F.image (Ideal.Quotient.mk J)
  have hF' : (F' : Set (A ⧸ J)) = Ideal.Quotient.mk J '' F := Finset.coe_image
  have hFq : IsOpen (Ideal.span (F' : Set (A ⧸ J)) : Set (A ⧸ J)) := by
    rw [hF', ← Ideal.map_span, Ideal.map_eq_image_of_surjective _ Ideal.Quotient.mk_surjective]
    exact (QuotientRing.isOpenQuotientMap_mk J).isOpenMap _ hF
  have hden := P.hasDenominatorPower_of_isOpen_span F s L hF
  have hden' := P.hasDenominatorPower_quotient J F s L hF' L' hden
  let _ := P.locUniformSpace F s L hden
  have _ := P.isUniformAddGroup_locUniformSpace F s L hden
  have _ := P.isTopologicalRing_locUniformSpace F s L hden
  have _ := P.isHuberRing_completion_locTopology F s L hden
  let _ := (P.quotient J).locUniformSpace F' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isUniformAddGroup_locUniformSpace F' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isTopologicalRing_locUniformSpace F' (Ideal.Quotient.mk J s) L' hden'
  have _ := (P.quotient J).isHuberRing_completion_locTopology F' (Ideal.Quotient.mk J s) L' hden'
  let S₁ := P.rationalLocalizationPair S hP F s L hden
  have hS₁ := isSheafyForEveryPresentation_rationalLocalizationPair P S hP F s L hden hF hS
  have hS₂ := isSheafyForEveryPresentation_rationalLocalizationPair (P.quotient J) (S.quotient J)
    hPq F' (Ideal.Quotient.mk J s) L' hden' hFq hSJ
  -- Identify the quotient localization with `S₁.quotient K` along the quotient mapping `π`
  let π := P.completionLocQuotientPairHom J F s L hF' L' S hP hden
  have hq := P.isQuotientMapping_completionLocQuotientPairHom J F s L hF' L' S hP hden
  let K := RingHom.ker π.toRingHom
  obtain ⟨hSK, eSK, hT2K, hcompK, heSK⟩ := quotientKer_of_isQuotientMapping hq hS₂
  have hker_pow : ∀ {n : ℕ}, J ^ n = ⊥ → K ^ n = ⊥ := fun hJn ↦ by
    dsimp only [K]; rw [PairOfDefinition.toRingHom_completionLocQuotientPairHom,
      P.ker_completionLocQuotientHom J F s L hF' L' hden]
    exact Ideal.closure_pow_eq_bot (by rw [← Ideal.map_pow, hJn, Ideal.map_bot])
  -- Compare the open immersions and verify the commutative pullback square
  have hv_open := isOpenImmersion_comapOfPair_toCompletionLocHom P S hP F s L hden hF hS hS₁
  have hv_range := range_comapOfPair_toCompletionLocHom P S hP F s L hden hS hS₁
  have hu₀_open := isOpenImmersion_comapOfPair_toCompletionLocHom (P.quotient J) (S.quotient J)
    hPq F' _ L' hden' hFq hSJ hS₂
  have hu₀_range := range_comapOfPair_toCompletionLocHom (P.quotient J) (S.quotient J)
    hPq F' _ L' hden' hSJ hS₂
  let u₀ := comapOfPair hSJ hS₂ ((P.quotient J).toCompletionLocHom (S.quotient J) hPq F' _ L' hden')
  have hu_range : Set.range (eSK.hom ≫ u₀).hom.base =
      (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base ⁻¹' (O : Set (ofPair S hS).obj) := by
    have hsurj : Function.Surjective eSK.hom.hom.base :=
      (TopCat.homeoOfIso (forgetToTop.mapIso ((ObjectProperty.ι isAdic).mapIso eSK))).surjective
    rw [ObjectProperty.FullSubcategory.comp_hom, comp_base, TopCat.coe_comp, hsurj.range_comp,
      hu₀_range]
    simpa only [Pair.Hom.toRingHom_quotientHom, F', O, Opens.coe_mk] using
      (comapOfPair_base_preimage_spaBasicOpen hS hSJ (Pair.quotientHom S J) F s).symm
  have hψπ : hq.quotientKerInverse.comp π = Pair.quotientHom S₁ K := by
    rw [← Pair.Hom.quotientLift_comp_quotientHom K π le_rfl, ← Pair.Hom.comp_assoc,
      hq.quotientKerInverse_comp_quotientLift, Pair.Hom.id_comp]
  have hpair_sq : (Pair.quotientHom S₁ K).comp (P.toCompletionLocHom S hP F s L hden) =
      (hq.quotientKerInverse.comp
        ((P.quotient J).toCompletionLocHom (S.quotient J) hPq F' _ L' hden')).comp
          (Pair.quotientHom S J) := by
    rw [← hψπ, Pair.Hom.comp_assoc,
      P.completionLocQuotientPairHom_comp_toCompletionLocHom J F s L hF' L' S hP hden,
      ← Pair.Hom.comp_assoc]
  have hsq : comapOfPair hS₁ hSK (Pair.quotientHom S₁ K) ≫
      comapOfPair hS hS₁ (P.toCompletionLocHom S hP F s L hden) =
      (eSK.hom ≫ u₀) ≫ comapOfPair hS hSJ (Pair.quotientHom S J) := by
    simpa only [comapOfPair_comp hS hS₁ hSK, comapOfPair_comp hS hSJ hSK,
      comapOfPair_comp hSJ hS₂ hSK, ← heSK] using congrArg (comapOfPair hS hSK) hpair_sq
  exact ⟨{
    Ring := UniformSpace.Completion L
    pair := S₁
    isSheafy := hS₁
    ideal := K
    isSheafyQuotient := hSK
    completeSpaceQuotient := hcompK
    pow_eq_bot := hker_pow
    targetMap := _
    quotientMap := eSK.hom ≫ u₀
    range_targetMap := hv_range
    range_quotientMap := hu_range
    comm := hsq }⟩

/-- **Pullback square over a neighbourhood** for an ideal quotient `S.quotient J` of a sheafy Huber
pair `(A, S)` around a point `z` in an open `W` of `ofPair S hS`: an open neighbourhood
`openSet ≤ W` containing `z` together with an `OfPairQuotientOpenSquare` over `openSet`. -/
structure OfPairQuotientRationalSquare {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] (S : Pair A)
    (hS : IsSheafyForEveryPresentation S.plus) (J : Ideal A)
    (hSJ : IsSheafyForEveryPresentation (S.quotient J).plus)
    (W : Opens (ofPair S hS).obj) (z : (ofPair S hS).obj) where
  /-- The open neighbourhood of `z` contained in `W`. -/
  openSet : Opens (ofPair S hS).obj
  /-- Membership of `z` in `openSet`. -/
  mem : z ∈ openSet
  /-- Containment of `openSet` in `W`. -/
  le : openSet ≤ W
  /-- The pullback square over `openSet`. -/
  square : OfPairQuotientOpenSquare S hS J hSJ openSet

/-- **Existence of a pullback square over a neighbourhood for an ideal quotient of a sheafy Huber
pair.** Around any point `z` in an open `W` of `ofPair S hS`, there is an open neighbourhood
`openSet ≤ W` of `z` carrying an `OfPairQuotientOpenSquare`, packaged as
`OfPairQuotientRationalSquare S hS J hSJ W z`. -/
theorem exists_ofPair_quotient_rational_square (S : Pair A)
    (hS : IsSheafyForEveryPresentation S.plus) (J : Ideal A)
    (hSJ : IsSheafyForEveryPresentation (S.quotient J).plus)
    (W : Opens (ofPair S hS).obj) {z : (ofPair S hS).obj} (hz : z ∈ W) :
    Nonempty (OfPairQuotientRationalSquare S hS J hSJ W z) := by
  -- Choose a rational open `O ≤ W` around `z` and apply `exists_ofPair_quotient_open_square`
  let W_spa : Opens (spa S.plus) := ⟨(ofPairHomeomorph S hS).symm ⁻¹' (W : Set (ofPair S hS).obj),
    W.isOpen.preimage (ofPairHomeomorph S hS).symm.continuous⟩
  have hz_spa : ofPairHomeomorph S hS z ∈ W_spa := Set.mem_preimage.mpr (by simpa using hz)
  obtain ⟨R₀, hR₀, hzR₀, hR₀W⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens S.plus) hz_spa
  obtain ⟨F, s, hF, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hR₀
  let O : Opens (ofPair S hS).obj :=
    ⟨ofPairHomeomorph S hS ⁻¹' (spaBasicOpen S.plus F s : Set (spa S.plus)),
      (spaBasicOpen S.plus F s).isOpen.preimage (ofPairHomeomorph S hS).continuous⟩
  have hOW : O ≤ W := fun y hy ↦ by
    have hy' : (ofPairHomeomorph S hS).symm (ofPairHomeomorph S hS y) ∈ (W : Set _) := hR₀W hy
    rwa [(ofPairHomeomorph S hS).symm_apply_apply] at hy'
  obtain ⟨sq⟩ := exists_ofPair_quotient_open_square S hS J hSJ F s hF
  exact ⟨{ openSet := O, mem := hzR₀, le := hOW, square := sq }⟩

namespace OfPairQuotientOpenSquare

variable {S : Pair A} {hS : IsSheafyForEveryPresentation S.plus} {J : Ideal A}
  {hSJ : IsSheafyForEveryPresentation (S.quotient J).plus} {O₀ : Opens (ofPair S hS).obj}

/-- **Restriction of the quotient closed immersion over `O₀`** agrees with the local quotient
closed immersion of an `OfPairQuotientOpenSquare` over `O₀`, conjugated by the range-identification
isomorphisms. -/
theorem restrictPreimage_quotientHom (sq : OfPairQuotientOpenSquare S hS J hSJ O₀) :
    (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.restrictPreimage O₀ =
      (IsOpenImmersion.isoRestrictOfRangeEq sq.quotientMap.hom sq.range_quotientMap).inv ≫
        (comapOfPair sq.isSheafy sq.isSheafyQuotient
          (Pair.quotientHom sq.pair sq.ideal)).hom ≫
        (IsOpenImmersion.isoRestrictOfRangeEq sq.targetMap.hom sq.range_targetMap).hom :=
  (Iso.eq_inv_comp (IsOpenImmersion.isoRestrictOfRangeEq sq.quotientMap.hom
    sq.range_quotientMap)).mpr
    (comm_restrictPreimage_of_square sq.comm O₀
      (IsOpenImmersion.isoRestrictOfRangeEq_hom_ofRestrict sq.targetMap.hom sq.range_targetMap)
      (IsOpenImmersion.isoRestrictOfRangeEq_hom_ofRestrict sq.quotientMap.hom
        sq.range_quotientMap)).symm

/-- **Compatibility of `liftToRestrict` with `restrictPreimage`** on an `OfPairQuotientOpenSquare`
whose `targetMap` and `quotientMap` land in `O` and its preimage. -/
theorem quotientHom_comp_liftToRestrict (sq : OfPairQuotientOpenSquare S hS J hSJ O₀)
    {O : Opens (ofPair S hS).obj}
    (hmT : Set.range sq.targetMap.hom.base ⊆ (O : Set (ofPair S hS).obj))
    (hmQ : Set.range sq.quotientMap.hom.base ⊆
      (((Opens.map (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base).obj O :
        Opens (ofPair (S.quotient J) hSJ).obj) : Set (ofPair (S.quotient J) hSJ).obj)) :
    (comapOfPair sq.isSheafy sq.isSheafyQuotient (Pair.quotientHom sq.pair sq.ideal)).hom ≫
        sq.targetMap.hom.liftToRestrict hmT =
      sq.quotientMap.hom.liftToRestrict hmQ ≫
        (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.restrictPreimage O :=
  comm_restrictPreimage_of_square sq.comm O
    (Hom.liftToRestrict_ofRestrict _ _) (Hom.liftToRestrict_ofRestrict _ _)

/-- **Any point of an open `O` lying in `O₀` lies in the image of
`sq.targetMap.hom.liftToRestrict`** for an `OfPairQuotientOpenSquare` over `O₀`. -/
theorem mem_range_liftToRestrict_targetMap (sq : OfPairQuotientOpenSquare S hS J hSJ O₀)
    {O : Opens (ofPair S hS).obj} {p : (ofPair S hS).obj.restrict O.isOpenEmbedding}
    (hp : p.val ∈ O₀) (ht : Set.range sq.targetMap.hom.base ⊆ (O : Set (ofPair S hS).obj)) :
    p ∈ Set.range (sq.targetMap.hom.liftToRestrict ht).base := by
  obtain ⟨q, hq⟩ : p.val ∈ Set.range sq.targetMap.hom.base := sq.range_targetMap.symm ▸ hp
  exact ⟨q, Subtype.ext (by simp [hq])⟩

/-- **Compatibility of a morphism `gO` on `O ≥ O₀` with `g₀` along
`sq.targetMap.hom.liftToRestrict`**: if `gO` restricts to `g₀` along the quotient closed immersion,
then pulling `gO` back along `sq.targetMap` and the local quotient immersion agrees with pulling
`g₀` back along `sq.quotientMap`. -/
theorem quotientHom_comp_liftToRestrict_comp (sq : OfPairQuotientOpenSquare S hS J hSJ O₀)
    {Y : PreAdicSpace.{u}} (g₀ : (ofPair (S.quotient J) hSJ).obj ⟶ Y)
    {O : Opens (ofPair S hS).obj} (hO₀O : O₀ ≤ O)
    (hmT : Set.range sq.targetMap.hom.base ⊆ (O : Set (ofPair S hS).obj))
    {gO : (ofPair S hS).obj.restrict O.isOpenEmbedding ⟶ Y}
    (hgO_ι : (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.restrictPreimage O ≫ gO =
      (ofPair (S.quotient J) hSJ).obj.ofRestrict
        ((Opens.map (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base).obj O).isOpenEmbedding ≫
        g₀) :
    (comapOfPair sq.isSheafy sq.isSheafyQuotient (Pair.quotientHom sq.pair sq.ideal)).hom ≫
        sq.targetMap.hom.liftToRestrict hmT ≫ gO =
      sq.quotientMap.hom ≫ g₀ := by
  have hmQ : Set.range sq.quotientMap.hom.base ⊆
      (((Opens.map (comapOfPair hS hSJ (Pair.quotientHom S J)).hom.base).obj O :
        Opens (ofPair (S.quotient J) hSJ).obj) : Set (ofPair (S.quotient J) hSJ).obj) :=
    sq.range_quotientMap.le.trans (Set.preimage_mono (SetLike.coe_subset_coe.mpr hO₀O))
  rw [reassoc_of% (sq.quotientHom_comp_liftToRestrict hmT hmQ), hgO_ι,
    Hom.liftToRestrict_ofRestrict_assoc]

end OfPairQuotientOpenSquare

end TauCeti.AdicSpace
