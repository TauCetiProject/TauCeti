/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.AnalyticLocus
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FinitePresentation.Cancel

import Mathlib.RingTheory.RingHom.FinitePresentation
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Emptiness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete
import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType

/-!
# Analytic, noetherian, and discrete affinoid comparisons for `LocallyOfFinitePresentation`

Specializes `TauCeti.AdicSpace.LocallyOfFinitePresentation` to analytic and noetherian targets
(`locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ`,
`locallyOfFinitePresentation_iff_locallyOfFiniteType_of_forall_discrete_isNoetherianRing`,
`LocallyOfFiniteType.locallyOfFinitePresentation_analyticLocusMap`), general and strongly noetherian
Tate affinoids (`locallyOfFinitePresentation_comapOfPair`,
`locallyOfFinitePresentation_comapOfPair_of_isTateRing`), and discrete affinoids
(`locallyOfFinitePresentation_comapOfPair_discrete_iff`).

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces* (1996), §1.1–1.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37 and Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber Huber.PairOfDefinition PreAdicSpace ValuationSpectrum CompleteAffinoidOpen

universe u

variable {X Y : AdicSpace.{u}}

theorem locallyOfFinitePresentation_iff_locallyOfFiniteType_of_forall_discrete_isNoetherianRing
    {f : X ⟶ Y} (hY : Y.IsLocallyHuberStandard)
    (hnoeth : ∀ (A : Type u) [CommRing A] [UniformSpace A] [IsUniformAddGroup A]
      [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A] [DiscreteTopology A]
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (k : presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y.obj),
      PreAdicSpace.IsOpenImmersion k → IsNoetherianRing A) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f := by
  refine ⟨LocallyOfFinitePresentation.locallyOfFiniteType,
    fun hf ↦ (locallyOfFinitePresentation_iff f).mpr fun x ↦ ?_⟩
  obtain ⟨V, hV, hfxV⟩ := isLocallyHuberStandard_iff.mp hY (f.hom.base x)
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isHuberStandardAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      (ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy))
  let kY := eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding
  have : PreAdicSpace.IsOpenImmersion kY := PreAdicSpace.IsOpenImmersion.comp _ _
  have ha₀ : kY.base (eV.hom.base ⟨f.hom.base x, hfxV⟩) = f.hom.base x := by
    have hb : (eV.hom ≫ eV.inv).base ⟨f.hom.base x, hfxV⟩ = ⟨f.hom.base x, hfxV⟩ := by simp; rfl
    exact congrArg (Y.obj.ofRestrict V.isOpenEmbedding).base hb
  obtain ⟨TA, sA, hTA, -, CX, β, hβ, c₀, hc₀, hsq⟩ :=
    hf.exists_openImmersion_over_rationalLocalization P hP hsheafA kY x ha₀
  let CY₁ := ofRationalLocalization P hP hsheafA kY TA sA hTA
  have : IsHuberStandard CY₁.Ring := .of_isTopologicallyFiniteType
    (isTopologicallyFiniteType_toRationalLocalizationHom P hP hsheafA kY TA sA
      hTA).isTopologicallyFiniteType_toRingHom
  refine exists_locallyOfFinitePresentation_chart_of_openImmersion_sq CY₁ CX β hβ (fun _ ↦ ?_) hc₀
    hsq
  have : IsNoetherianRing CY₁.Ring := hnoeth CY₁.Ring CY₁.pair CY₁.pod CY₁.le_plus CY₁.hom
    CY₁.isOpenImmersion
  have : DiscreteTopology CX.Ring := hβ.isTopologicallyFiniteType_toRingHom.discreteTopology
  exact RingHom.FinitePresentation.of_finiteType.mp
    hβ.isTopologicallyFiniteType_toRingHom.finiteType

/-- **Over an analytic target locally of Huber's standing class, `LocallyOfFinitePresentation` and
`LocallyOfFiniteType` coincide** (Huber 1996, §1.2). -/
theorem locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    {f : X ⟶ Y} (hY : Y.IsLocallyHuberStandard) (ha : Y.obj.analyticPoints = Set.univ) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f := by
  refine locallyOfFinitePresentation_iff_locallyOfFiniteType_of_forall_discrete_isNoetherianRing hY
    fun A _ _ _ _ _ _ _ _ S P hP k hk ↦ ?_
  have := hk
  rcases (spa S.plus).eq_empty_or_nonempty with hemp | ⟨a₁, ha₁⟩
  · have : Subsingleton A :=
      (spa_eq_empty_iff_subsingleton S.plus S.isRingOfIntegralElements).mp hemp
    infer_instance
  · let a₀ : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP := ⟨a₁, ha₁⟩
    have ha₀ : a₀ ∈ (presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP).analyticPoints := by
      rw [← preimage_analyticPoints_of_isOpenImmersion k, ha]; exact Set.mem_univ _
    rw [analyticPoints_presentationLimitPreAdicSpace] at ha₀
    exact ((isAnalyticPoint_def _).mp ((mem_spaAnalytic_iff S.plus _).mp ha₀).2
      (isOpen_discrete _)).elim

namespace IsLocallyNoetherian

theorem locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    {f : X ⟶ Y} (hY : Y.IsLocallyNoetherian) (ha : Y.obj.analyticPoints = Set.univ) :
    LocallyOfFinitePresentation f ↔ LocallyOfFiniteType f :=
  AdicSpace.locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    (hY.isLocallyHuberStandard_of_analyticPoints_eq_univ ha) ha

end IsLocallyNoetherian

theorem LocallyOfFiniteType.locallyOfFinitePresentation_analyticLocusMap {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (hY : Y.IsLocallyNoetherian) :
    LocallyOfFinitePresentation hf.isAdic.analyticLocusMap := by
  have haY : Y.analyticLocus.obj.analyticPoints = Set.univ := by
    rw [analyticLocus_obj, analyticPoints_analyticLocus]
  exact (locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    hY.isLocallyHuberStandard_analyticLocus haY).mpr (hf.restrict hf.isAdic.analyticLocusMap_ι)

section Affinoid

theorem locallyOfFinitePresentation_comapOfPresentation {A B : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A]
    [IsHuberStandard A] [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation) :
    LocallyOfFinitePresentation (comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) :=
  (locallyOfFinitePresentation_iff _).mpr fun x ↦
    exists_locallyOfFinitePresentation_chart_of_openImmersion_sq
      { Ring := A, pair := S, pod := P, le_plus := hS, isSheaf := hsheafS, hom := 𝟙 _ }
      { Ring := B, pair := T, pod := P', le_plus := hT, isSheaf := hsheafT, hom := 𝟙 _ }
      φ hφ hfp (b₀ := x) rfl (by simp)

theorem locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) (P' : PairOfDefinition B)
    (hP' : P'.ringOfDefinition ≤ T.plus) (φ : Pair.Hom S T) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) ↔
      LocallyOfFinitePresentation
        (comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso (@LocallyOfFinitePresentation.{u}) _
      (ofPairIsoOfPresentation S hS P hP).hom,
    ← ofPairIsoOfPresentation_hom_comapOfPresentation hS hT P hP P' hP' φ,
    MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFinitePresentation.{u})]

theorem locallyOfFinitePresentation_comapOfPair {A B : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A]
    [IsHuberStandard A] [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  exact (locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mpr
    (locallyOfFinitePresentation_comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP'
      (hT.isSheaf P' hP') φ hφ hfp)

theorem locallyOfFinitePresentation_comapOfPair_of_isTateRing {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A] [IsStronglyNoetherian A]
    [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  rw [locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ]
  exact (locallyOfFinitePresentation_iff_locallyOfFiniteType_of_analyticPoints_eq_univ
    (IsLocallyHuberStandard.spa P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP
      (hS.isSheaf P hP))
    (analyticPoints_presentationLimitPreAdicSpace_of_isTateRing P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)).mpr
    (locallyOfFiniteType_comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP')
      φ hφ)

theorem LocallyOfFinitePresentation.finitePresentation_of_discreteTopology {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] {S : Pair A} {T : Pair B}
    {hS : IsSheafyForEveryPresentation S.plus} {hT : IsSheafyForEveryPresentation T.plus}
    {φ : Pair.Hom S T} (hf : LocallyOfFinitePresentation (comapOfPair hS hT φ)) :
    φ.toRingHom.FinitePresentation := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  have hsheafA := hS.isSheaf P hP
  have hq := (locallyOfFinitePresentation_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP'
    φ).mp hf
  let CA : CompleteAffinoidOpen (ofPresentation S P hP hsheafA).obj :=
    { Ring := A, pair := S, pod := P, le_plus := hP, isSheaf := hsheafA, hom := 𝟙 _ }
  refine (finiteType_and_finitePresentation_of_forall_rational_chart_discrete P hP hsheafA P' hP'
    (hT.isSheaf P' hP') φ True fun y ↦ ?_).2 trivial
  obtain ⟨TA, sA, hTA, -, -, CX, β, hβ, hβ_fp, c₀, hc₀, hsq⟩ :=
    hq.exists_openImmersion_over_rationalLocalization CA y rfl
  exact ⟨TA, sA, hTA, CX, β, hβ, c₀, hc₀, hsq, fun _ ↦ hβ_fp
    (isTopologicallyFiniteType_toRationalLocalizationHom P hP hsheafA (𝟙 _) TA sA
      hTA).isTopologicallyFiniteType_toRingHom.discreteTopology⟩

/-- **Discrete affinoid comparison for `LocallyOfFinitePresentation`**. -/
theorem locallyOfFinitePresentation_comapOfPair_discrete_iff {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    (hS : IsSheafyForEveryPresentation (Pair.discrete A).plus)
    (hT : IsSheafyForEveryPresentation (Pair.discrete B).plus)
    (φ : Pair.Hom (Pair.discrete A) (Pair.discrete B)) :
    LocallyOfFinitePresentation (comapOfPair hS hT φ) ↔ φ.toRingHom.FinitePresentation := by
  refine ⟨fun hf ↦ hf.finitePresentation_of_discreteTopology, fun hφ ↦ ?_⟩
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity B := IsRightUniformAddGroup.discreteUniformity
  exact locallyOfFinitePresentation_comapOfPair hS hT φ
    ((Pair.Hom.isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top
      Pair.discrete_plus Pair.discrete_plus).mpr (RingHom.FiniteType.of_finitePresentation hφ))
    fun _ ↦ hφ

end Affinoid

end TauCeti.AdicSpace
