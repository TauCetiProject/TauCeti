/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.PlusWeaklyFiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.Target
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Discrete

import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.RingHom.FiniteType
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Discreteness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Morphisms of adic spaces locally of finite type

Defines `TauCeti.AdicSpace.LocallyOfFiniteType` (Huber 1996, Definition 1.2.1(i); Wedhorn,
Definition 8.48(1)) and proves Wedhorn's Proposition 8.50 (`comp`, `isMultiplicative`, `of_comp`,
`restrict`) together with `locallyOfFiniteType_comapOfPair_discrete_iff`.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces* (1996), §1.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), §8.42, §8.48–8.50.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber Huber.PairOfDefinition PreAdicSpace ValuationSpectrum

universe u

/-- **Morphisms locally of finite type** (Huber 1996, Definition 1.2.1(i); Wedhorn,
Definition 8.48(1)). -/
def LocallyOfFiniteType : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  PreAdicSpace.LocallyOfFiniteType f.hom

variable {X Y Z : AdicSpace.{u}}

theorem locallyOfFiniteType_iff_chartLocally (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ chartLocally (fun φ ↦ φ.IsTopologicallyFiniteType) f.hom :=
  locallyOfFiniteType_iff f.hom

theorem LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) : LocallyOfPlusWeaklyFiniteType f :=
  PreAdicSpace.LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType hf

theorem LocallyOfFiniteType.locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) : LocallyOfWeaklyFiniteType f :=
  PreAdicSpace.LocallyOfFiniteType.locallyOfWeaklyFiniteType hf

theorem LocallyOfFiniteType.isAdic {f : X ⟶ Y} (hf : LocallyOfFiniteType f) : IsAdic f :=
  hf.locallyOfWeaklyFiniteType.isAdic

theorem LocallyOfFiniteType.isLocallyNoetherian_source {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (hY : Y.IsLocallyNoetherian) : X.IsLocallyNoetherian :=
  hY.of_locallyOfFiniteType hf

theorem LocallyOfFiniteType.isLocallyHuberStandard_source {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (hY : Y.IsLocallyHuberStandard) : X.IsLocallyHuberStandard :=
  hY.of_locallyOfFiniteType hf

instance LocallyOfFiniteType.containsIdentities :
    LocallyOfFiniteType.{u}.ContainsIdentities where
  id_mem X := locallyOfFiniteType_id X.property

instance LocallyOfFiniteType.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
  MorphismProperty.RespectsIso.inverseImage
    (@PreAdicSpace.LocallyOfFiniteType.{u}) (ObjectProperty.ι PreAdicSpace.isAdic)

theorem LocallyOfFiniteType.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] : LocallyOfFiniteType f :=
  locallyOfFiniteType_of_isOpenImmersion f.hom X.property

theorem LocallyOfFiniteType.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] : LocallyOfFiniteType f :=
  (locallyOfFiniteType_iff_chartLocally f).mpr <| (chartLocally_iff _).mpr fun x ↦ isEmptyElim x

/-- A complete Hausdorff sheafy affinoid open immersion `Spa(A, A⁺) ⟶ X` in `PreAdicSpace`. -/
structure CompleteAffinoidOpen (X_sp : PreAdicSpace.{u}) where
  /-- Underlying complete Hausdorff Huber ring. -/
  Ring : Type u
  [commRing : CommRing Ring]
  [uniformSpace : UniformSpace Ring]
  [isUniformAddGroup : IsUniformAddGroup Ring]
  [isTopologicalRing : IsTopologicalRing Ring]
  [completeSpace : CompleteSpace Ring]
  [t2Space : T2Space Ring]
  [isHuberRing : IsHuberRing Ring]
  /-- Underlying Huber pair. -/
  pair : Pair Ring
  /-- Compatible pair of definition. -/
  pod : PairOfDefinition Ring
  /-- Compatibility `A₀ ≤ A⁺`. -/
  le_plus : pod.ringOfDefinition ≤ pair.plus
  /-- Sheafiness of the presentation-limit structure presheaf. -/
  isSheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa pair.plus))
    (presentationLimitPresheaf pod pair.plus)
  /-- Open immersion into `X_sp`. -/
  hom : presentationLimitPreAdicSpace pod pair.plus
    pair.isRingOfIntegralElements.isPowerBounded_of_mem le_plus ⟶ X_sp
  [isOpenImmersion : PreAdicSpace.IsOpenImmersion hom]

attribute [instance] CompleteAffinoidOpen.commRing CompleteAffinoidOpen.uniformSpace
  CompleteAffinoidOpen.isUniformAddGroup CompleteAffinoidOpen.isTopologicalRing
  CompleteAffinoidOpen.completeSpace CompleteAffinoidOpen.t2Space CompleteAffinoidOpen.isHuberRing
  CompleteAffinoidOpen.isOpenImmersion

namespace CompleteAffinoidOpen

/-- Underlying affinoid `PreAdicSpace` of a `CompleteAffinoidOpen`. -/
noncomputable abbrev space {X_sp : PreAdicSpace.{u}} (C : CompleteAffinoidOpen X_sp) :
    PreAdicSpace.{u} :=
  presentationLimitPreAdicSpace C.pod C.pair.plus
    C.pair.isRingOfIntegralElements.isPowerBounded_of_mem C.le_plus

/-- Morphism `CX.space ⟶ CY.space` induced by `CY.pair → CX.pair`. -/
noncomputable abbrev pairComap {X_sp Y_sp : PreAdicSpace.{u}}
    (CY : CompleteAffinoidOpen Y_sp) (CX : CompleteAffinoidOpen X_sp)
    (φ : Pair.Hom CY.pair CX.pair) : CX.space ⟶ CY.space :=
  presentationLimitPreAdicSpacePairComap CY.pod CX.pod CY.le_plus CX.le_plus CX.isSheaf φ

section OfRationalLocalization

variable {Y_sp : PreAdicSpace.{u}} {A : Type u} [CommRing A] [TopologicalSpace A]
  [IsTopologicalRing A] [IsHuberRing A] {S : Pair A} (P : PairOfDefinition A)
  (hP : P.ringOfDefinition ≤ S.plus)
  (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
    (presentationLimitPresheaf P S.plus))
  (kY : presentationLimitPreAdicSpace P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y_sp) [PreAdicSpace.IsOpenImmersion kY]
  (T : Finset A) (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A))

/-- Complete affinoid open obtained by restricting `kY : Spa(S) ⟶ Y` to `R(T / s)`. -/
noncomputable def ofRationalLocalization : CompleteAffinoidOpen Y_sp :=
  let L := Localization.Away s; let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  letI := P.locUniformSpace T s L hden; haveI := P.isUniformAddGroup_locUniformSpace T s L hden
  haveI := P.isTopologicalRing_locUniformSpace T s L hden
  haveI := P.isHuberRing_completion_locTopology T s L hden
  let S₁ := P.rationalLocalizationPair S hP T s L hden
  let P₁ := P.completionLocalization T s L hden
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP T s L hden
  have hsheaf₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP T s L hden hT
    hsheaf
  let ι := presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheaf₁
    (P.toCompletionLocHom S hP T s L hden)
  haveI : PreAdicSpace.IsOpenImmersion ι := by
    dsimp only [ι]; rw [presentationLimitPreAdicSpacePairComap_def]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP T s L hden hT
      hsheaf₁
  { Ring := UniformSpace.Completion L, pair := S₁, pod := P₁, le_plus := hP₁, isSheaf := hsheaf₁
    hom := ι ≫ kY, isOpenImmersion := PreAdicSpace.IsOpenImmersion.comp ι kY }

/-- Canonical pair morphism `S → (ofRationalLocalization P hP hsheaf kY T s hT).pair`. -/
noncomputable def toRationalLocalizationHom :
    Pair.Hom S (ofRationalLocalization P hP hsheaf kY T s hT).pair :=
  let L := Localization.Away s; let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  letI := P.locUniformSpace T s L hden; haveI := P.isUniformAddGroup_locUniformSpace T s L hden
  haveI := P.isTopologicalRing_locUniformSpace T s L hden
  haveI := P.isHuberRing_completion_locTopology T s L hden
  P.toCompletionLocHom S hP T s L hden

/-- Open immersion into `Spa(S)` of `ofRationalLocalization`. -/
noncomputable abbrev toRationalLocalizationComap :
    (ofRationalLocalization P hP hsheaf kY T s hT).space ⟶
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP :=
  presentationLimitPreAdicSpacePairComap P (ofRationalLocalization P hP hsheaf kY T s hT).pod hP
    (ofRationalLocalization P hP hsheaf kY T s hT).le_plus
    (ofRationalLocalization P hP hsheaf kY T s hT).isSheaf
    (toRationalLocalizationHom P hP hsheaf kY T s hT)

theorem ofRationalLocalization_hom :
    (ofRationalLocalization P hP hsheaf kY T s hT).hom =
      toRationalLocalizationComap P hP hsheaf kY T s hT ≫ kY := by rfl

theorem range_toRationalLocalizationComap_base :
    Set.range (toRationalLocalizationComap P hP hsheaf kY T s hT).base =
      (spaBasicOpen S.plus T s : Set (spa S.plus)) := by
  rw [toRationalLocalizationComap, presentationLimitPreAdicSpacePairComap_def]
  exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P hP T s
    (Localization.Away s) (P.hasDenominatorPower_of_isOpen_span T s (Localization.Away s) hT) _

theorem isTopologicallyFiniteType_toRationalLocalizationHom :
    (toRationalLocalizationHom P hP hsheaf kY T s hT).IsTopologicallyFiniteType := by
  let L := Localization.Away s; have hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  let _ := P.locUniformSpace T s L hden; have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  exact P.isTopologicallyFiniteType_toCompletionLocHom S hP T s L hden
    (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hT)

theorem finitePresentation_toRationalLocalizationHom [DiscreteTopology A] :
    (toRationalLocalizationHom P hP hsheaf kY T s hT).toRingHom.FinitePresentation := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let L := Localization.Away s; have hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  let _ := P.locUniformSpace T s L hden; have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  dsimp only [toRationalLocalizationHom]; rw [toRingHom_toCompletionLocHom]
  exact P.finitePresentation_toCompletionLoc_of_discreteTopology (T : Set A) s L hden

theorem exists_ringEquiv_away_of_discrete [DiscreteTopology A] :
    ∃ e : Localization.Away s ≃+* (ofRationalLocalization P hP hsheaf kY T s hT).Ring,
      e.symm.toRingHom.comp (toRationalLocalizationHom P hP hsheaf kY T s hT).toRingHom =
        algebraMap A (Localization.Away s) := by
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let L := Localization.Away s; let hden := P.hasDenominatorPower_of_isOpen_span T s L hT
  let _ := P.locUniformSpace T s L hden; have _ := P.isUniformAddGroup_locUniformSpace T s L hden
  have _ := P.isTopologicalRing_locUniformSpace T s L hden
  have _ := P.isHuberRing_completion_locTopology T s L hden
  refine ⟨P.completionLocEquivOfDiscreteTopology (T : Set A) s L hden, RingHom.ext fun a ↦ ?_⟩
  have ha : (P.toCompletionLocHom S hP T s L hden).toRingHom a =
      (algebraMap A L a : UniformSpace.Completion L) := by
    rw [toRingHom_toCompletionLocHom, toCompletionLoc_apply]
  exact (congrArg (P.completionLocEquivOfDiscreteTopology (T : Set A) s L hden).symm ha).trans
    (P.completionLocEquivOfDiscreteTopology_symm_coe (T : Set A) s L hden (algebraMap A L a))

theorem exists_ofRationalLocalization_lift {Z_sp : PreAdicSpace.{u}}
    (D : CompleteAffinoidOpen Z_sp) (g : Y_sp ⟶ Z_sp)
    {a₀ : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP} {d₀ : D.space}
    (had : (kY ≫ g).base a₀ = D.hom.base d₀) :
    ∃ (T : Finset A) (s : A) (hT : IsOpen (Ideal.span (T : Set A) : Set A)),
      a₀ ∈ spaBasicOpen S.plus T s ∧
      let CY₁ := ofRationalLocalization P hP hsheaf kY T s hT
      ∃ (a₁ : CY₁.space) (α : Pair.Hom D.pair CY₁.pair),
        CY₁.hom.base a₁ = kY.base a₀ ∧ D.pairComap CY₁ α ≫ D.hom = CY₁.hom ≫ g := by
  let OA : Opens (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
    ⟨(kY ≫ g).base ⁻¹' Set.range D.hom.base,
      D.hom.isOpenEmbedding.isOpen_range.preimage (kY ≫ g).base.hom.2⟩
  have ha₀O : a₀ ∈ OA := ⟨d₀, had.symm⟩
  obtain ⟨RA, hRA, ha₀R, hRAO⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens S.plus) ha₀O
  obtain ⟨T, s, hT, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRA
  refine ⟨T, s, hT, ha₀R, ?_⟩
  let CY₁ := ofRationalLocalization P hP hsheaf kY T s hT
  let ι := toRationalLocalizationComap P hP hsheaf kY T s hT
  have hrange_ι := range_toRationalLocalizationComap_base P hP hsheaf kY T s hT
  obtain ⟨a₁, ha₁⟩ : (a₀ : spa S.plus) ∈ Set.range ι.base :=
    hrange_ι.symm ▸ (ha₀R : (a₀ : spa S.plus) ∈ (spaBasicOpen S.plus T s : Set (spa S.plus)))
  have hsub : Set.range (CY₁.hom ≫ g).base ⊆ Set.range D.hom.base := by
    rintro _ ⟨z, rfl⟩; rw [ofRationalLocalization_hom, Category.assoc]
    exact hRAO (hrange_ι ▸ ⟨z, rfl⟩ :
      (ι.base z : spa S.plus) ∈ (spaBasicOpen S.plus T s : Set (spa S.plus)))
  let l := PreAdicSpace.IsOpenImmersion.lift D.hom (CY₁.hom ≫ g) hsub
  refine ⟨a₁, presentationLimitHomPairHom D.pod CY₁.pod D.pair CY₁.pair D.le_plus CY₁.le_plus l,
    by rw [ofRationalLocalization_hom]; exact congrArg kY.base ha₁, ?_⟩
  rw [pairComap, presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom D.pod CY₁.pod
    D.pair CY₁.pair D.le_plus CY₁.le_plus CY₁.isSheaf]
  exact PreAdicSpace.IsOpenImmersion.lift_fac D.hom (CY₁.hom ≫ g) hsub

end OfRationalLocalization

/-- Restrict a `CompleteAffinoidOpen` to `R(T / s)`. -/
noncomputable abbrev rationalShrink {X_sp : PreAdicSpace.{u}}
    (C : CompleteAffinoidOpen X_sp) (T : Finset C.Ring) (s : C.Ring)
    (hT : IsOpen (Ideal.span (T : Set C.Ring) : Set C.Ring)) : CompleteAffinoidOpen X_sp :=
  ofRationalLocalization C.pod C.le_plus C.isSheaf C.hom T s hT

/-- Canonical pair morphism `C.pair → (C.rationalShrink T s hT).pair`. -/
noncomputable abbrev toRationalShrinkHom {X_sp : PreAdicSpace.{u}}
    (C : CompleteAffinoidOpen X_sp) (T : Finset C.Ring) (s : C.Ring)
    (hT : IsOpen (Ideal.span (T : Set C.Ring) : Set C.Ring)) :
    Pair.Hom C.pair (C.rationalShrink T s hT).pair :=
  toRationalLocalizationHom C.pod C.le_plus C.isSheaf C.hom T s hT

end CompleteAffinoidOpen

section OpenImmersionCharts

open CompleteAffinoidOpen

theorem exists_rational_shrink_lift_sq {X_sp Y_sp Z_sp : PreAdicSpace.{u}}
    {f_hom : X_sp ⟶ Y_sp} {g_hom : Y_sp ⟶ Z_sp} {x : X_sp}
    (CZ : CompleteAffinoidOpen Z_sp) (CY : CompleteAffinoidOpen Y_sp)
    {C : Type u} [CommRing C] [TopologicalSpace C] [IsTopologicalRing C] [IsHuberRing C]
    {U : Pair C} (PC : PairOfDefinition C) (hPC : PC.ringOfDefinition ≤ U.plus)
    (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
      (presentationLimitPresheaf PC U.plus))
    (kX : presentationLimitPreAdicSpace PC U.plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem hPC ⟶ X_sp) [PreAdicSpace.IsOpenImmersion kX]
    (ψ : Pair.Hom CZ.pair CY.pair) (χ : Pair.Hom CZ.pair U) (hχ : χ.IsTopologicallyFiniteType)
    {b₀ : CY.space} (hb₀ : CY.hom.base b₀ = f_hom.base x)
    {c₀ : presentationLimitPreAdicSpace PC U.plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem hPC} (hc₀ : kX.base c₀ = x)
    (hsq_g : CZ.pairComap CY ψ ≫ CZ.hom = CY.hom ≫ g_hom)
    (hsq_fg : presentationLimitPreAdicSpacePairComap CZ.pod PC CZ.le_plus hPC hsheafC χ ≫ CZ.hom =
      kX ≫ f_hom ≫ g_hom) :
    ∃ (TC : Finset C) (sC : C) (hTC : IsOpen (Ideal.span (TC : Set C) : Set C)),
      let CX₁ := ofRationalLocalization PC hPC hsheafC kX TC sC hTC
      ∃ (φ : Pair.Hom CY.pair CX₁.pair) (_ : φ.IsTopologicallyFiniteType) (c₁ : CX₁.space),
        CX₁.hom.base c₁ = x ∧ CY.pairComap CX₁ φ ≫ CY.hom = CX₁.hom ≫ f_hom ∧
        φ.comp ψ = (toRationalLocalizationHom PC hPC hsheafC kX TC sC hTC).comp χ := by
  obtain ⟨TC, sC, hTC, -, c₁, φ, hc₁, hsq_f⟩ := exists_ofRationalLocalization_lift PC hPC hsheafC
    kX CY f_hom (a₀ := c₀) (d₀ := b₀) (by simpa [hc₀] using hb₀.symm)
  let CX₁ := ofRationalLocalization PC hPC hsheafC kX TC sC hTC
  have hqψ : CY.pairComap CX₁ φ ≫ CZ.pairComap CY ψ =
      toRationalLocalizationComap PC hPC hsheafC kX TC sC hTC ≫
        presentationLimitPreAdicSpacePairComap CZ.pod PC CZ.le_plus hPC hsheafC χ := by
    rw [← cancel_mono CZ.hom, Category.assoc, hsq_g, ← Category.assoc, hsq_f,
      ofRationalLocalization_hom, Category.assoc, Category.assoc, ← hsq_fg, Category.assoc]
  have hφψ : φ.comp ψ = (toRationalLocalizationHom PC hPC hsheafC kX TC sC hTC).comp χ := by
    have h := congrArg (presentationLimitHomPairHom CZ.pod CX₁.pod CZ.pair CX₁.pair CZ.le_plus
      CX₁.le_plus) hqψ
    rwa [← presentationLimitPreAdicSpacePairComap_comp CZ.pod CY.pod CX₁.pod CZ.le_plus CY.le_plus
        CX₁.le_plus CY.isSheaf CX₁.isSheaf,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap CZ.pod CX₁.pod CZ.pair
        CX₁.pair CZ.le_plus CX₁.le_plus CX₁.isSheaf,
      ← presentationLimitPreAdicSpacePairComap_comp CZ.pod PC CX₁.pod CZ.le_plus hPC CX₁.le_plus
        hsheafC CX₁.isSheaf,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap CZ.pod CX₁.pod CZ.pair
        CX₁.pair CZ.le_plus CX₁.le_plus CX₁.isSheaf] at h
  exact ⟨TC, sC, hTC, φ, .of_comp (hφψ ▸
    (isTopologicallyFiniteType_toRationalLocalizationHom PC hPC hsheafC kX TC sC hTC).comp hχ),
    c₁, hc₁.trans hc₀, hsq_f, hφψ⟩

private theorem LocallyOfFiniteType.exists_complete_openImmersion_chart {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (x : X.obj) :
    ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
      (φ : Pair.Hom CY.pair CX.pair) (_ : φ.IsTopologicallyFiniteType) (b₀ : CX.space),
      CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom := by
  classical
  obtain ⟨U, hxU, V, -, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheafB, eU, eV, hfac⟩ := (chartLocally_iff f.hom).mp
      ((locallyOfFiniteType_iff_chartLocally f).mp hf) x
  have hT1 : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A) := by simp
  let T' : Finset B := ({1} : Finset A).image φ.toRingHom; let s' : B := φ.toRingHom 1
  have hT1' : IsOpen (Ideal.span (T' : Set B) : Set B) := by simp [T']
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      (ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy))
  let L := Localization.Away (1 : A); let L' := Localization.Away s'
  have hden := P.hasDenominatorPower_denom_one ({1} : Finset A) L
  have hden' := P'.hasDenominatorPower_of_isOpen_span T' s' L' hT1'
  let _ := P.locUniformSpace ({1} : Finset A) 1 L hden
  have _ := P.isUniformAddGroup_locUniformSpace ({1} : Finset A) 1 L hden
  have _ := isTopologicalRing_locUniformSpace P ({1} : Finset A) 1 L hden
  have _ := P.isHuberRing_completion_locTopology ({1} : Finset A) 1 L hden
  let _ := P'.locUniformSpace T' s' L' hden'
  have _ := P'.isUniformAddGroup_locUniformSpace T' s' L' hden'
  have _ := P'.isTopologicalRing_locUniformSpace T' s' L' hden'
  have _ := P'.isHuberRing_completion_locTopology T' s' L' hden'
  let S₁ := P.rationalLocalizationPair S hP ({1} : Finset A) 1 L hden
  let P₁ := P.completionLocalization ({1} : Finset A) 1 L hden
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP {1} 1 L hden
  have hsheaf₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP {1} 1 L hden
    hT1 hsheafA
  let T₁ := P'.rationalLocalizationPair T hP' T' s' L' hden'
  let P'₁ := P'.completionLocalization T' s' L' hden'
  have hP'₁ : P'₁.ringOfDefinition ≤ T₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring T.plus hP' T' s' L'
      hden'
  have hsheaf'₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P' T hP' T' s' L'
    hden' hT1' hsheafB
  obtain ⟨eA, heA⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P hP
      ({1} : Finset A) 1 L hden hT1 (fun y ↦ by rw [rationalSubset_singleton_one]; exact y.2)
      hsheaf₁
  obtain ⟨eB, heB⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P' hP' T' s' L'
      hden' hT1' (fun y ↦ by
        simp only [T', s', Finset.image_singleton, map_one, rationalSubset_singleton_one]
        exact y.2) hsheaf'₁
  let kY := eA.hom ≫ eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding
  let kX := eB.hom ≫ eU.inv ≫ X.obj.ofRestrict U.isOpenEmbedding
  have : PreAdicSpace.IsOpenImmersion (eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding) := .comp _ _
  have : PreAdicSpace.IsOpenImmersion kY := .comp _ _
  have : PreAdicSpace.IsOpenImmersion (eU.inv ≫ X.obj.ofRestrict U.isOpenEmbedding) := .comp _ _
  have : PreAdicSpace.IsOpenImmersion kX := .comp _ _
  let CY : CompleteAffinoidOpen Y.obj :=
    { Ring := UniformSpace.Completion L, pair := S₁, pod := P₁, le_plus := hP₁, isSheaf := hsheaf₁,
      hom := kY }
  let CX : CompleteAffinoidOpen X.obj :=
    { Ring := UniformSpace.Completion L', pair := T₁, pod := P'₁, le_plus := hP'₁,
      isSheaf := hsheaf'₁, hom := kX }
  let φ₁ : Pair.Hom CY.pair CX.pair := P.completionLocPairMap S hP ({1} : Finset A) 1 L hden P' T
    hP' φ T' s' L' hden' rfl (fun _ ht ↦ Finset.mem_image_of_mem _ ht)
  have hφ₁ : φ₁.IsTopologicallyFiniteType :=
    P.isTopologicallyFiniteType_completionLocPairMap S hP ({1} : Finset A) 1 L hden P' T hP' φ T'
      s' L' hden' rfl (fun _ ht ↦ Finset.mem_image_of_mem _ ht) hφ
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hT1')
  have hcomm := presentationLimitPreAdicSpaceComap_completionLocPairMap_comp P P' hP hP' φ
    hsheafB ({1} : Finset A) 1 L hden L' hden' hsheaf₁ hsheaf'₁
  refine ⟨CY, CX, φ₁, hφ₁, eB.inv.base (eU.hom.base ⟨x, hxU⟩), ?_, ?_⟩
  · have hb : (eU.hom ≫ eB.inv ≫ eB.hom ≫ eU.inv).base ⟨x, hxU⟩ = ⟨x, hxU⟩ := by simp; rfl
    exact congrArg (X.obj.ofRestrict U.isOpenEmbedding).base hb
  · rw [← heA, ← heB] at hcomm
    dsimp only [CY, CX, kY, kX, pairComap, φ₁, T', s']
    rw [presentationLimitPreAdicSpacePairComap_def, Category.assoc, Category.assoc, hfac,
      Iso.inv_hom_id_assoc, ← Category.assoc _ eA.hom, hcomm, Category.assoc]

private theorem locallyOfFiniteType_of_forall_openImmersion_sq {f : X ⟶ Y}
    (h : ∀ x : X.obj, ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
      (φ : Pair.Hom CY.pair CX.pair) (_ : φ.IsTopologicallyFiniteType) (b₀ : CX.space),
      CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom) :
    LocallyOfFiniteType f := by
  choose CY CX φ hφ b₀ hb₀ hsq using h
  let U (x : X.obj) : Opens X.obj :=
    ⟨Set.range (CX x).hom.base, (CX x).hom.isOpenEmbedding.isOpen_range⟩
  refine PreAdicSpace.LocallyOfFiniteType.of_iSup_eq_top U
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, b₀ x, hb₀ x⟩) fun x ↦ ?_
  have heU := PreAdicSpace.IsOpenImmersion.isoOfRangeEq_hom_comp
    (X.obj.ofRestrict (U x).isOpenEmbedding) (CX x).hom (Opens.set_range_inclusion' (U x))
  have h1 : PreAdicSpace.LocallyOfFiniteType ((CX x).hom ≫ f.hom) := by
    rw [← hsq x, pairComap, presentationLimitPreAdicSpacePairComap_def]
    exact (ValuationSpectrum.locallyOfFiniteType_presentationLimitPreAdicSpaceComap (CY x).pod
      (CX x).pod (CY x).le_plus (CX x).le_plus (CX x).isSheaf (φ x)
      (hφ x)).comp_of_isOpenImmersion (CY x).hom
  rwa [← heU, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u}]

theorem LocallyOfFiniteType.exists_openImmersion_over_rationalLocalization {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {S : Pair A} (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (kY : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y.obj) [PreAdicSpace.IsOpenImmersion kY]
    (x : X.obj) {a₀ : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP} (ha₀ : kY.base a₀ = f.hom.base x) :
    ∃ (TA : Finset A) (sA : A) (hTA : IsOpen (Ideal.span (TA : Set A) : Set A)),
      a₀ ∈ spaBasicOpen S.plus TA sA ∧
      let CY₁ := ofRationalLocalization P hP hsheafA kY TA sA hTA
      ∃ (CX : CompleteAffinoidOpen X.obj) (β : Pair.Hom CY₁.pair CX.pair)
        (_ : β.IsTopologicallyFiniteType) (c₀ : CX.space),
        CX.hom.base c₀ = x ∧ CY₁.pairComap CX β ≫ CY₁.hom = CX.hom ≫ f.hom := by
  obtain ⟨CY', CX₀, φ', hφ', c₀₀, hc₀₀, hsq'⟩ := hf.exists_complete_openImmersion_chart x
  have had : (kY ≫ 𝟙 Y.obj).base a₀ = CY'.hom.base ((CY'.pairComap CX₀ φ').base c₀₀) := by
    simpa [hc₀₀, ha₀] using (congrArg (fun m ↦ m.base c₀₀) hsq').symm
  obtain ⟨TA, sA, hTA, ha₀R, a₁, α₁, ha₁, hsq_α⟩ :=
    exists_ofRationalLocalization_lift P hP hsheafA kY CY' (𝟙 Y.obj) had
  obtain ⟨TC, sC, hTC, β, hβ_tft, c₁, hc₁, hsq, -⟩ :=
    exists_rational_shrink_lift_sq (f_hom := f.hom) (g_hom := 𝟙 Y.obj) CY'
      (ofRationalLocalization P hP hsheafA kY TA sA hTA) CX₀.pod CX₀.le_plus CX₀.isSheaf CX₀.hom
      α₁ φ' hφ' (ha₁.trans ha₀) hc₀₀ hsq_α (by simpa using hsq')
  exact ⟨TA, sA, hTA, ha₀R, CX₀.rationalShrink TC sC hTC, β, hβ_tft, c₁, hc₁, hsq⟩

/-- **Composition of morphisms locally of finite type** (Wedhorn, Proposition 8.50(1)). -/
theorem LocallyOfFiniteType.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyOfFiniteType f) (hg : LocallyOfFiniteType g) :
    LocallyOfFiniteType (f ≫ g) := by
  refine locallyOfFiniteType_of_forall_openImmersion_sq fun x ↦ ?_
  obtain ⟨CZ, CY, ψ, hψ, b₀, hb₀, hsq_g⟩ :=
    hg.exists_complete_openImmersion_chart (f.hom.base x)
  obtain ⟨TB, sB, hTB, -, CX, β, hβ, c₀, hc₀, hsq_f⟩ :=
    hf.exists_openImmersion_over_rationalLocalization CY.pod CY.le_plus CY.isSheaf CY.hom x hb₀
  let CY₁ := CY.rationalShrink TB sB hTB
  let ψ₁ := (CY.toRationalShrinkHom TB sB hTB).comp ψ
  have hψ₁ := (isTopologicallyFiniteType_toRationalLocalizationHom CY.pod CY.le_plus CY.isSheaf
    CY.hom TB sB hTB).comp hψ
  refine ⟨CZ, CX, β.comp ψ₁, hβ.comp hψ₁, c₀, hc₀, ?_⟩
  rw [pairComap, presentationLimitPreAdicSpacePairComap_comp CZ.pod CY₁.pod CX.pod CZ.le_plus
      CY₁.le_plus CX.le_plus CY₁.isSheaf CX.isSheaf,
    presentationLimitPreAdicSpacePairComap_comp CZ.pod CY.pod CY₁.pod CZ.le_plus CY.le_plus
      CY₁.le_plus CY.isSheaf CY₁.isSheaf,
    Category.assoc, Category.assoc, hsq_g, ← Category.assoc _ CY.hom,
    ← ofRationalLocalization_hom, ← Category.assoc, hsq_f, Category.assoc,
    ObjectProperty.FullSubcategory.comp_hom]

instance LocallyOfFiniteType.isStableUnderComposition :
    LocallyOfFiniteType.{u}.IsStableUnderComposition where
  comp_mem _ _ hf hg := hf.comp hg

instance LocallyOfFiniteType.isMultiplicative :
    LocallyOfFiniteType.{u}.IsMultiplicative where

/-- **Right-cancellation of morphisms locally of finite type** (Wedhorn, Proposition 8.50(2)). -/
theorem LocallyOfFiniteType.of_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : LocallyOfFiniteType (f ≫ g)) : LocallyOfFiniteType f := by
  classical
  refine locallyOfFiniteType_of_forall_openImmersion_sq fun x ↦ ?_
  obtain ⟨CZ, CX, χ, hχ, c₀, hc₀, hsq_fg⟩ := hfg.exists_complete_openImmersion_chart x
  let OY : Opens Y.obj :=
    ⟨g.hom.base ⁻¹' Set.range CZ.hom.base,
      CZ.hom.isOpenEmbedding.isOpen_range.preimage g.hom.base.hom.2⟩
  have hfxO : f.hom.base x ∈ OY :=
    ⟨(CZ.pairComap CX χ).base c₀, by simpa [hc₀] using congrArg (fun m ↦ m.base c₀) hsq_fg⟩
  obtain ⟨W, hW, hfxW, hWO⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affinoidOpens Y.property.isLocallyAffinoid) hfxO
  obtain ⟨B, _, _, _, _, _, _, _, T, P', hP', hsheafB, ⟨eW⟩⟩ :=
    Y.property.isSheafy.exists_complete_isSheaf_of_mem_affinoidOpens hW
  let kY := eW.inv ≫ Y.obj.ofRestrict W.isOpenEmbedding
  have : PreAdicSpace.IsOpenImmersion kY := PreAdicSpace.IsOpenImmersion.comp _ _
  let CY : CompleteAffinoidOpen Y.obj :=
    { Ring := B, pair := T, pod := P', le_plus := hP', isSheaf := hsheafB, hom := kY }
  have hb₀ : CY.hom.base (eW.hom.base ⟨f.hom.base x, hfxW⟩) = f.hom.base x := by
    have hb : (eW.hom ≫ eW.inv).base ⟨f.hom.base x, hfxW⟩ = ⟨f.hom.base x, hfxW⟩ := by simp; rfl
    exact congrArg (Y.obj.ofRestrict W.isOpenEmbedding).base hb
  have hrangeY : Set.range (CY.hom ≫ g.hom).base ⊆ Set.range CZ.hom.base := by
    rintro _ ⟨b, rfl⟩; exact hWO (eW.inv.base b).2
  let p := PreAdicSpace.IsOpenImmersion.lift CZ.hom (CY.hom ≫ g.hom) hrangeY
  let ψ := presentationLimitHomPairHom CZ.pod CY.pod CZ.pair CY.pair CZ.le_plus CY.le_plus p
  have hsq_g : CZ.pairComap CY ψ ≫ CZ.hom = CY.hom ≫ g.hom := by
    rw [pairComap, presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom CZ.pod CY.pod
      CZ.pair CY.pair CZ.le_plus CY.le_plus CY.isSheaf]
    exact PreAdicSpace.IsOpenImmersion.lift_fac CZ.hom (CY.hom ≫ g.hom) hrangeY
  obtain ⟨TC, sC, hTC, φ, hφ, c₁, hc₁, hsq_f, -⟩ :=
    exists_rational_shrink_lift_sq (f_hom := f.hom) (g_hom := g.hom) CZ CY CX.pod CX.le_plus
      CX.isSheaf CX.hom ψ χ hχ hb₀ hc₀ hsq_g hsq_fg
  exact ⟨CY, CX.rationalShrink TC sC hTC, φ, hφ, c₁, hc₁, hsq_f⟩

/-- **Restriction of `LocallyOfFiniteType` along open immersions of the source**. -/
theorem LocallyOfFiniteType.restrict {U V : AdicSpace.{u}} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} {g : U ⟶ V} [PreAdicSpace.IsOpenImmersion iU.hom]
    (hcomm : g ≫ iV = iU ≫ f) (hf : LocallyOfFiniteType f) : LocallyOfFiniteType g :=
  LocallyOfFiniteType.of_comp (g := iV)
    (hcomm ▸ (LocallyOfFiniteType.of_isOpenImmersion iU).comp hf)

end OpenImmersionCharts

section Affinoid

open CompleteAffinoidOpen

theorem locallyOfFiniteType_comapOfPresentation {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFiniteType (comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) := by
  unfold LocallyOfFiniteType
  rw [comapOfPresentation_hom, presentationLimitPreAdicSpacePairComap_def]
  exact ValuationSpectrum.locallyOfFiniteType_presentationLimitPreAdicSpaceComap P P' hS hT hsheafT
    φ hφ

theorem locallyOfFiniteType_comapOfPair_iff_comapOfPresentation {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) (P' : PairOfDefinition B)
    (hP' : P'.ringOfDefinition ≤ T.plus) (φ : Pair.Hom S T) :
    LocallyOfFiniteType (comapOfPair hS hT φ) ↔
      LocallyOfFiniteType
        (comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso (@LocallyOfFiniteType.{u}) _
      (ofPairIsoOfPresentation S hS P hP).hom,
    ← ofPairIsoOfPresentation_hom_comapOfPresentation hS hT P hP P' hP' φ,
    MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType.{u})]

theorem locallyOfFiniteType_comapOfPair {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [UniformSpace B] [IsUniformAddGroup B]
    [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFiniteType (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  exact (locallyOfFiniteType_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mpr
    (locallyOfFiniteType_comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP')
      φ hφ)

theorem finiteType_and_finitePresentation_of_forall_rational_chart_discrete
    {A B : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    {S : Pair A} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    {T : Pair B} (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (φ : Pair.Hom S T) (Q : Prop)
    (hchart : ∀ y : (ofPresentation T P' hP' hsheafB).obj,
      ∃ (TA : Finset A) (sA : A) (hTA : IsOpen (Ideal.span (TA : Set A) : Set A)),
        let CY₁ := ofRationalLocalization P hP hsheafA (𝟙 (ofPresentation S P hP hsheafA).obj) TA
          sA hTA
        ∃ (CX : CompleteAffinoidOpen (ofPresentation T P' hP' hsheafB).obj)
          (β : Pair.Hom CY₁.pair CX.pair) (_ : β.IsTopologicallyFiniteType) (c₀ : CX.space),
          CX.hom.base c₀ = y ∧
          CY₁.pairComap CX β ≫ CY₁.hom =
            CX.hom ≫ (comapOfPresentation S P hP hsheafA T P' hP' hsheafB φ).hom ∧
          (Q → β.toRingHom.FinitePresentation)) :
    φ.toRingHom.FiniteType ∧ (Q → φ.toRingHom.FinitePresentation) := by
  classical
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity B := IsRightUniformAddGroup.discreteUniformity
  have hγ_id {D₁ D₂ : CompleteAffinoidOpen (ofPresentation T P' hP' hsheafB).obj}
      (f₁ : D₁.space ⟶ D₂.space) (f₂ : D₂.space ⟶ D₁.space) (hf : f₁ ≫ f₂ = 𝟙 D₁.space) (x) :
      (presentationLimitHomPairHom D₂.pod D₁.pod D₂.pair D₁.pair D₂.le_plus D₁.le_plus f₁).toRingHom
        ((presentationLimitHomPairHom D₁.pod D₂.pod D₁.pair D₂.pair D₁.le_plus D₂.le_plus
          f₂).toRingHom x) = x := by
    have h : (presentationLimitHomPairHom D₂.pod D₁.pod D₂.pair D₁.pair D₂.le_plus D₁.le_plus
        f₁).comp (presentationLimitHomPairHom D₁.pod D₂.pod D₁.pair D₂.pair D₁.le_plus D₂.le_plus
        f₂) = Pair.Hom.id D₁.pair := by
      rw [← presentationLimitHomPairHom_comp D₁.pod D₂.pod D₁.pod D₁.pair D₂.pair D₁.pair
        D₁.le_plus D₂.le_plus D₁.le_plus f₁ f₂, hf,
        presentationLimitHomPairHom_id D₁.pod D₁.pair D₁.le_plus]
    simpa using RingHom.congr_fun (congrArg Pair.Hom.toRingHom h) x
  have hloc (y : spa T.plus) : ∃ (TB : Finset B) (sB : B),
      y.1 ∈ rationalSubset T.plus TB sB ∧
      ((algebraMap B (Localization.Away sB)).comp φ.toRingHom).FiniteType ∧
      (Q → ((algebraMap B (Localization.Away sB)).comp φ.toRingHom).FinitePresentation) := by
    let y₀ : (ofPresentation T P' hP' hsheafB).obj := y
    obtain ⟨TA, sA, hTA, CX, β, hβ, c₀, hc₀, hsq, hQβ⟩ := hchart y₀
    let CY₁ := ofRationalLocalization P hP hsheafA (𝟙 (ofPresentation S P hP hsheafA).obj) TA sA
      hTA
    let ιA := toRationalLocalizationHom P hP hsheafA (𝟙 (ofPresentation S P hP hsheafA).obj) TA sA
      hTA
    let α := β.comp ιA
    have hα_tft := hβ.comp (isTopologicallyFiniteType_toRationalLocalizationHom P hP hsheafA
      (𝟙 _) TA sA hTA)
    obtain ⟨hDiscC, hα_ft⟩ := isTopologicallyFiniteType_iff_discreteTopology_and_finiteType.mp
      hα_tft.isTopologicallyFiniteType_toRingHom
    have : DiscreteTopology CX.Ring := hDiscC
    have hsq_α : presentationLimitPreAdicSpacePairComap P CX.pod hP CX.le_plus CX.isSheaf α =
        CX.hom ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
      rw [presentationLimitPreAdicSpacePairComap_comp P CY₁.pod CX.pod hP CY₁.le_plus CX.le_plus
        CY₁.isSheaf CX.isSheaf]
      rw [ofRationalLocalization_hom, Category.comp_id, comapOfPresentation_hom] at hsq; exact hsq
    let OB : Opens (ofPresentation T P' hP' hsheafB).obj :=
      ⟨Set.range CX.hom.base, CX.hom.isOpenEmbedding.isOpen_range⟩
    have hyO : y₀ ∈ OB := ⟨c₀, hc₀⟩
    obtain ⟨RB, hRB, hyR, hRBO⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens T.plus) hyO
    obtain ⟨TB, sB, hTB, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRB
    let CT := ofRationalLocalization P' hP' hsheafB (𝟙 _) TB sB hTB
    have hCT_range : Set.range CT.hom.base = (spaBasicOpen T.plus TB sB : Set (spa T.plus)) := by
      rw [ofRationalLocalization_hom, Category.comp_id]
      exact range_toRationalLocalizationComap_base P' hP' hsheafB (𝟙 _) TB sB hTB
    let δ := presentationLimitHomPairHom P' CX.pod T CX.pair hP' CX.le_plus CX.hom
    have hkX_eq := (presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom P' CX.pod T
      CX.pair hP' CX.le_plus CX.isSheaf CX.hom).symm
    let TC : Finset CX.Ring := TB.image δ.toRingHom; let sC : CX.Ring := δ.toRingHom sB
    have hTC : IsOpen (Ideal.span (TC : Set CX.Ring) : Set CX.Ring) := isOpen_discrete _
    let CX₁ := CX.rationalShrink TC sC hTC
    let ιC := toRationalLocalizationComap CX.pod CX.le_plus CX.isSheaf CX.hom TC sC hTC
    have hιC_range := range_toRationalLocalizationComap_base CX.pod CX.le_plus CX.isSheaf CX.hom TC
      sC hTC
    have hpre_eq : (spaBasicOpen CX.pair.plus TC sC : Set (spa CX.pair.plus)) =
        CX.hom.base ⁻¹' (spaBasicOpen T.plus TB sB : Set (spa T.plus)) := by
      ext c
      have hc_eq : (CX.hom.base c : spa T.plus) = δ.spaComap c := by
        rw [hkX_eq]
        exact presentationLimitPreAdicSpacePairComap_base_apply P' CX.pod hP' CX.le_plus CX.isSheaf
          δ c
      exact ⟨fun hc ↦ Set.mem_preimage.mpr (hc_eq.symm ▸ mem_spaBasicOpen.mpr
          ((Set.ext_iff.mp (δ.spaComap_preimage_rationalSubset TB sB) c).mpr
            (mem_spaBasicOpen.mp hc))),
        fun hc ↦ mem_spaBasicOpen.mpr
          ((Set.ext_iff.mp (δ.spaComap_preimage_rationalSubset TB sB) c).mp
            (mem_spaBasicOpen.mp (hc_eq ▸ Set.mem_preimage.mp hc)))⟩
    have hrange_eq : Set.range CX₁.hom.base = Set.range CT.hom.base := by
      rw [ofRationalLocalization_hom, PreAdicSpace.comp_base, TopCat.coe_comp, Set.range_comp,
        hιC_range, hpre_eq, hCT_range]
      exact Set.image_preimage_eq_iff.mpr hRBO
    let eCB := PreAdicSpace.IsOpenImmersion.isoOfRangeEq CX₁.hom CT.hom hrange_eq
    have heCB_inv := PreAdicSpace.IsOpenImmersion.isoOfRangeEq_inv_comp CX₁.hom CT.hom hrange_eq
    let γ₁ := presentationLimitHomPairHom CX₁.pod CT.pod CX₁.pair CT.pair CX₁.le_plus CT.le_plus
      eCB.inv
    have hγ₁_bij : Function.Bijective γ₁.toRingHom :=
      Function.bijective_iff_has_inverse.mpr
        ⟨_, hγ_id eCB.hom eCB.inv eCB.hom_inv_id, hγ_id eCB.inv eCB.hom eCB.inv_hom_id⟩
    have hpath : γ₁.comp ((CX.toRationalShrinkHom TC sC hTC).comp α) =
        (toRationalLocalizationHom P' hP' hsheafB (𝟙 _) TB sB hTB).comp φ := by
      have hsq' : eCB.inv ≫ ιC ≫
          presentationLimitPreAdicSpacePairComap P CX.pod hP CX.le_plus CX.isSheaf α =
          toRationalLocalizationComap P' hP' hsheafB (𝟙 _) TB sB hTB ≫
            presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
        have heCB' : eCB.inv ≫ ιC ≫ CX.hom =
            toRationalLocalizationComap P' hP' hsheafB (𝟙 _) TB sB hTB :=
          heCB_inv.trans
            (Category.comp_id (toRationalLocalizationComap P' hP' hsheafB (𝟙 _) TB sB hTB))
        rw [hsq_α, ← Category.assoc ιC, ← Category.assoc eCB.inv, heCB']
      have h := congrArg (presentationLimitHomPairHom P CT.pod S CT.pair hP CT.le_plus) hsq'
      dsimp only [γ₁, ιC, toRationalLocalizationComap] at h ⊢
      rwa [← presentationLimitPreAdicSpacePairComap_comp P CX.pod CX₁.pod hP CX.le_plus CX₁.le_plus
          CX.isSheaf CX₁.isSheaf,
        presentationLimitHomPairHom_comp P CX₁.pod CT.pod S CX₁.pair CT.pair hP CX₁.le_plus
          CT.le_plus,
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P CX₁.pod S CX₁.pair hP
          CX₁.le_plus CX₁.isSheaf,
        ← presentationLimitPreAdicSpacePairComap_comp P P' CT.pod hP hP' CT.le_plus hsheafB
          CT.isSheaf,
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P CT.pod S CT.pair hP
          CT.le_plus CT.isSheaf] at h
    have hfpA := finitePresentation_toRationalLocalizationHom P hP hsheafA (𝟙 _) TA sA hTA
    have hfpC := finitePresentation_toRationalLocalizationHom CX.pod CX.le_plus CX.isSheaf CX.hom TC
      sC hTC
    obtain ⟨eB, heB⟩ := exists_ringEquiv_away_of_discrete P' hP' hsheafB (𝟙 _) TB sB hTB
    have heq : (algebraMap B (Localization.Away sB)).comp φ.toRingHom =
        eB.symm.toRingHom.comp (γ₁.toRingHom.comp
          ((CX.toRationalShrinkHom TC sC hTC).toRingHom.comp α.toRingHom)) := by
      rw [← heB, RingHom.comp_assoc, ← Pair.Hom.toRingHom_comp, ← hpath]
      simp only [Pair.Hom.toRingHom_comp]
    refine ⟨TB, sB, mem_spaBasicOpen.mp hyR, ?_, fun hQ ↦ ?_⟩
    · rw [heq]
      exact (RingHom.FiniteType.of_surjective _ eB.symm.surjective).comp
        ((RingHom.FiniteType.of_surjective _ hγ₁_bij.surjective).comp
          ((RingHom.FiniteType.of_finitePresentation hfpC).comp hα_ft))
    · rw [heq, Pair.Hom.toRingHom_comp]
      exact (RingHom.FinitePresentation.of_bijective eB.symm.bijective).comp
        ((RingHom.FinitePresentation.of_bijective hγ₁_bij).comp
          (hfpC.comp ((hQβ hQ).comp hfpA)))
  choose TB sB hyR hft hfp using hloc
  have : IsLocalization.Away (1 : B) B := IsLocalization.self (by rintro _ ⟨n, rfl⟩; simp)
  have hcov : rationalSubset T.plus ({1} : Finset B) 1 ⊆
      ⋃ y : spa T.plus, rationalSubset T.plus (TB y) (sB y) := fun v hv ↦ by
    rw [rationalSubset_singleton_one] at hv; exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hyR ⟨v, hv⟩⟩
  have hspan : Ideal.span (Set.range sB) = ⊤ := by
    simpa using span_eq_top_of_rationalSubset_subset_iUnion (Aplus := T.plus) (T := {1}) (s := 1) B
      (fun _ _ ↦ isOpen_discrete _) hcov
  exact ⟨RingHom.finiteType_ofLocalizationSpanTarget φ.toRingHom (Set.range sB) hspan
      (by rintro ⟨_, y, rfl⟩; exact hft y),
    fun hQ ↦ RingHom.finitePresentation_ofLocalizationSpanTarget φ.toRingHom (Set.range sB) hspan
      (by rintro ⟨_, y, rfl⟩; exact hfp y hQ)⟩

theorem LocallyOfFiniteType.finiteType_of_discreteTopology {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] {S : Pair A} {T : Pair B}
    {hS : IsSheafyForEveryPresentation S.plus} {hT : IsSheafyForEveryPresentation T.plus}
    {φ : Pair.Hom S T} (hf : LocallyOfFiniteType (comapOfPair hS hT φ)) :
    φ.toRingHom.FiniteType := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  have hq := (locallyOfFiniteType_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mp hf
  refine (finiteType_and_finitePresentation_of_forall_rational_chart_discrete P hP (hS.isSheaf P hP)
    P' hP' (hT.isSheaf P' hP') φ False fun y ↦ ?_).1
  obtain ⟨TA, sA, hTA, -, CX, β, hβ, c₀, hc₀, hsq⟩ :=
    hq.exists_openImmersion_over_rationalLocalization P hP (hS.isSheaf P hP) (𝟙 _) y rfl
  exact ⟨TA, sA, hTA, CX, β, hβ, c₀, hc₀, hsq, False.elim⟩

/-- **Discrete affinoid comparison for `LocallyOfFiniteType`**. -/
theorem locallyOfFiniteType_comapOfPair_discrete_iff {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    (hS : IsSheafyForEveryPresentation (Pair.discrete A).plus)
    (hT : IsSheafyForEveryPresentation (Pair.discrete B).plus)
    (φ : Pair.Hom (Pair.discrete A) (Pair.discrete B)) :
    LocallyOfFiniteType (comapOfPair hS hT φ) ↔ φ.toRingHom.FiniteType := by
  refine ⟨fun hf ↦ hf.finiteType_of_discreteTopology, fun hφ ↦ ?_⟩
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity B := IsRightUniformAddGroup.discreteUniformity
  exact locallyOfFiniteType_comapOfPair hS hT φ
    ((Pair.Hom.isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top
      Pair.discrete_plus Pair.discrete_plus).mpr hφ)

end Affinoid

end TauCeti.AdicSpace
