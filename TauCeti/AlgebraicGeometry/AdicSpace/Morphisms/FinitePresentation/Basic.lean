/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyHuberStandard

import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Morphisms of adic spaces locally of finite presentation

Defines `TauCeti.AdicSpace.LocallyOfFinitePresentation` (Huber 1996, (1.1.1) and
Definition 1.2.1(ii)) via complete Hausdorff Huber-pair charts with `IsHuberStandard A` and
`DiscreteTopology A → φ.toRingHom.FinitePresentation`, and proves hierarchy placement, source
regularity, stability under open immersions, isomorphisms, chart refinement, and composition.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces* (1996), §1.1–1.2.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37 and Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber Huber.PairOfDefinition PreAdicSpace ValuationSpectrum CompleteAffinoidOpen

universe u

variable {X Y Z : AdicSpace.{u}}

/-- Pointwise chart condition for `TauCeti.AdicSpace.LocallyOfFinitePresentation` at `x : X.obj`. -/
abbrev LocallyOfFinitePresentationAt (f : X ⟶ Y) (x : X.obj) : Prop :=
  ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj) (_ : U ≤ (Opens.map f.hom.base).obj V)
    (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
    (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
    (_ : IsHuberStandard A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
    (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
    (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
    (φ : Pair.Hom S T) (_ : φ.IsTopologicallyFiniteType)
    (_ : DiscreteTopology A → φ.toRingHom.FinitePresentation)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (eU : X.obj.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (eV : Y.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
    X.obj.ofRestrict _ ≫ f.hom =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
        Y.obj.ofRestrict _

/-- **Morphisms locally of finite presentation** (Huber 1996, Definition 1.2.1(ii)). -/
def LocallyOfFinitePresentation : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  ∀ x, LocallyOfFinitePresentationAt f x

theorem locallyOfFinitePresentation_iff (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔ ∀ x : X.obj, LocallyOfFinitePresentationAt f x :=
  Iff.rfl

theorem LocallyOfFinitePresentation.locallyOfFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfFiniteType f := by
  refine (locallyOfFiniteType_iff_chartLocally f).mpr <| (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hxU, V, hUV, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, -, hsheaf, eU, eV, hfac⟩ := hf x
  exact ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, hφ, hsheaf, eU, eV, hfac⟩

theorem LocallyOfFinitePresentation.locallyOfPlusWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfPlusWeaklyFiniteType f :=
  hf.locallyOfFiniteType.locallyOfPlusWeaklyFiniteType

theorem LocallyOfFinitePresentation.locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfWeaklyFiniteType f :=
  hf.locallyOfFiniteType.locallyOfWeaklyFiniteType

theorem LocallyOfFinitePresentation.isAdic {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : IsAdic f :=
  hf.locallyOfFiniteType.isAdic

theorem LocallyOfFinitePresentation.isLocallyHuberStandard_source {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : X.IsLocallyHuberStandard := by
  rw [isLocallyHuberStandard_iff]; intro x
  obtain ⟨U, hxU, _, -, A, _, _, _, _, _, _, _, _, _, _, _, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, -, -, eU, -, -⟩ := hf x
  have : IsHuberStandard B := .of_isTopologicallyFiniteType hφ.isTopologicallyFiniteType_toRingHom
  refine ⟨U, (mem_propOpens_iff _).mpr ((isHuberStandardAffinoid_iff _).mpr ?_), hxU⟩
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T, P', hP', ⟨eU⟩⟩

theorem LocallyOfFinitePresentation.isLocallyNoetherian_source {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : X.IsLocallyNoetherian :=
  hf.isLocallyHuberStandard_source.isLocallyNoetherian

theorem LocallyOfFinitePresentation.exists_openImmersion_chart {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (x : X.obj) :
    ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
      (_ : IsHuberStandard CY.Ring) (φ : Pair.Hom CY.pair CX.pair) (_ : φ.IsTopologicallyFiniteType)
      (_ : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) (b₀ : CX.space),
      CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom := by
  obtain ⟨U, hxU, V, -, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, hfp, hsheafB, eU, eV, hfac⟩ := hf x
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      (ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy))
  let kX := eU.inv ≫ X.obj.ofRestrict U.isOpenEmbedding
  let kY := eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding
  have : PreAdicSpace.IsOpenImmersion kX := PreAdicSpace.IsOpenImmersion.comp _ _
  have : PreAdicSpace.IsOpenImmersion kY := PreAdicSpace.IsOpenImmersion.comp _ _
  refine ⟨{ Ring := A, pair := S, pod := P, le_plus := hP, isSheaf := hsheafA, hom := kY },
    { Ring := B, pair := T, pod := P', le_plus := hP', isSheaf := hsheafB, hom := kX },
    inferInstance, φ, hφ, hfp, eU.hom.base ⟨x, hxU⟩, ?_, ?_⟩
  · have hb : (eU.hom ≫ eU.inv).base ⟨x, hxU⟩ = ⟨x, hxU⟩ := by simp; rfl
    exact congrArg (X.obj.ofRestrict U.isOpenEmbedding).base hb
  · dsimp only [kX, kY, pairComap]
    rw [presentationLimitPreAdicSpacePairComap_def, Category.assoc, hfac, Iso.inv_hom_id_assoc]

theorem exists_locallyOfFinitePresentation_chart_of_openImmersion_sq {f : X ⟶ Y} {x : X.obj}
    (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj) [IsHuberStandard CY.Ring]
    (φ : Pair.Hom CY.pair CX.pair) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation)
    {b₀ : CX.space} (hb₀ : CX.hom.base b₀ = x)
    (hsq : CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom) :
    LocallyOfFinitePresentationAt f x := by
  let U : Opens X.obj := ⟨Set.range CX.hom.base, CX.hom.isOpenEmbedding.isOpen_range⟩
  let V : Opens Y.obj := ⟨Set.range CY.hom.base, CY.hom.isOpenEmbedding.isOpen_range⟩
  have hUV : U ≤ (Opens.map f.hom.base).obj V := fun _ ⟨b, hb⟩ ↦
    hb ▸ ⟨(CY.pairComap CX φ).base b, congrArg (fun m ↦ m.base b) hsq⟩
  let eU := PreAdicSpace.IsOpenImmersion.isoOfRangeEq (X.obj.ofRestrict U.isOpenEmbedding) CX.hom
    (Opens.set_range_inclusion' U)
  let eV := PreAdicSpace.IsOpenImmersion.isoOfRangeEq (Y.obj.ofRestrict V.isOpenEmbedding) CY.hom
    (Opens.set_range_inclusion' V)
  have heU := PreAdicSpace.IsOpenImmersion.isoOfRangeEq_hom_comp
    (X.obj.ofRestrict U.isOpenEmbedding) CX.hom (Opens.set_range_inclusion' U)
  have heV := PreAdicSpace.IsOpenImmersion.isoOfRangeEq_inv_comp
    (Y.obj.ofRestrict V.isOpenEmbedding) CY.hom (Opens.set_range_inclusion' V)
  refine ⟨U, ⟨b₀, hb₀⟩, V, hUV, CY.Ring, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, CY.pair, CY.pod, CY.le_plus,
    CX.Ring, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, CX.pair, CX.pod, CX.le_plus, φ, hφ, hfp, CX.isSheaf, eU, eV, ?_⟩
  rw [← presentationLimitPreAdicSpacePairComap_def, heV, ← Category.assoc eU.hom,
    Category.assoc eU.hom, ← pairComap, hsq, ← Category.assoc, heU]

theorem LocallyOfFinitePresentation.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] (hY : Y.IsLocallyHuberStandard) :
    LocallyOfFinitePresentation f := fun x ↦ by
  let O : Opens Y.obj := ⟨Set.range f.hom.base, f.hom.isOpenEmbedding.isOpen_range⟩
  have hfxO : f.hom.base x ∈ O := ⟨x, rfl⟩
  obtain ⟨V, hV, hfxV, hVO⟩ := Opens.isBasis_iff_nbhd.mp hY.isBasis_huberStandardAffinoidOpens hfxO
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isHuberStandardAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    (isSheafy_presentationLimitPreAdicSpace_iff P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP).mp
      (ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy))
  let U : Opens X.obj := (Opens.map f.hom.base).obj V
  have hrange : Set.range (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom).base =
      Set.range (Y.obj.ofRestrict V.isOpenEmbedding).base := by
    ext y; refine ⟨?_, ?_⟩
    · rintro ⟨⟨x', hx'⟩, rfl⟩; exact ⟨⟨f.hom.base x', hx'⟩, rfl⟩
    · rintro ⟨⟨y', hy'⟩, rfl⟩; obtain ⟨x', rfl⟩ := hVO hy'; exact ⟨⟨x', hy'⟩, rfl⟩
  let eUV := PreAdicSpace.IsOpenImmersion.isoOfRangeEq
    (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom) (Y.obj.ofRestrict V.isOpenEmbedding) hrange
  have heUV := PreAdicSpace.IsOpenImmersion.isoOfRangeEq_hom_comp
    (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom) (Y.obj.ofRestrict V.isOpenEmbedding) hrange
  let eU := eUV ≪≫ eV
  refine ⟨U, hfxV, V, le_rfl, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, A, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    S, P, hP, Pair.Hom.id S, Pair.Hom.isTopologicallyFiniteType_id S,
    fun _ ↦ by simpa [Pair.Hom.toRingHom_id] using RingHom.FinitePresentation.id A,
    hsheafA, eU, eV, ?_⟩
  have hid := presentationLimitPreAdicSpacePairComap_id P hP hsheafA
  rw [presentationLimitPreAdicSpacePairComap_def] at hid
  rw [hid, Category.id_comp]
  simp only [eU, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc]; exact heUV.symm

theorem LocallyOfFinitePresentation.of_id (hX : X.IsLocallyHuberStandard) :
    LocallyOfFinitePresentation (𝟙 X) :=
  LocallyOfFinitePresentation.of_isOpenImmersion (𝟙 X) hX

theorem locallyOfFinitePresentation_id_iff :
    LocallyOfFinitePresentation (𝟙 X) ↔ X.IsLocallyHuberStandard :=
  ⟨fun h ↦ h.isLocallyHuberStandard_source, LocallyOfFinitePresentation.of_id⟩

theorem LocallyOfFinitePresentation.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] :
    LocallyOfFinitePresentation f := fun x ↦ isEmptyElim x

instance LocallyOfFinitePresentation.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) where
  precomp {X' X Y} i _ f hf x' := by
    let e : X'.obj ≅ X.obj := (ObjectProperty.ι _).mapIso (asIso i)
    have hi : i.hom = e.hom := rfl
    obtain ⟨CY, CX, _, φ, hφ, hfp, b₀, hb₀, hsq⟩ := hf.exists_openImmersion_chart (e.hom.base x')
    let CX' : CompleteAffinoidOpen X'.obj :=
      { Ring := CX.Ring, pair := CX.pair, pod := CX.pod, le_plus := CX.le_plus,
        isSheaf := CX.isSheaf, hom := CX.hom ≫ e.inv, isOpenImmersion := .comp _ _ }
    have hb₀' : CX'.hom.base b₀ = x' := by
      have he := congrArg (fun m : X'.obj ⟶ X'.obj ↦ m.base x') e.hom_inv_id
      rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply] at he
      dsimp only [CX']; rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply, hb₀]
      exact he.trans (by simp)
    refine exists_locallyOfFinitePresentation_chart_of_openImmersion_sq CY CX' φ hφ hfp hb₀' ?_
    rw [ObjectProperty.FullSubcategory.comp_hom (f := i) (g := f), hi]
    dsimp only [CX', pairComap]; rw [Category.assoc, Iso.inv_hom_id_assoc]; exact hsq
  postcomp {X Y Y'} i _ f hf x := by
    let e : Y.obj ≅ Y'.obj := (ObjectProperty.ι _).mapIso (asIso i)
    have hi : i.hom = e.hom := rfl
    obtain ⟨CY, CX, hStd, φ, hφ, hfp, b₀, hb₀, hsq⟩ := hf.exists_openImmersion_chart x
    let CY' : CompleteAffinoidOpen Y'.obj :=
      { Ring := CY.Ring, pair := CY.pair, pod := CY.pod, le_plus := CY.le_plus,
        isSheaf := CY.isSheaf, hom := CY.hom ≫ e.hom, isOpenImmersion := .comp _ _ }
    have : IsHuberStandard CY'.Ring := hStd
    refine exists_locallyOfFinitePresentation_chart_of_openImmersion_sq CY' CX φ hφ hfp hb₀ ?_
    rw [ObjectProperty.FullSubcategory.comp_hom (f := f) (g := i), hi]
    dsimp only [CY', pairComap]; rw [← Category.assoc, hsq, Category.assoc]

theorem finitePresentation_of_comp_eq_toRationalShrinkHom_comp
    {X_sp Y_sp Z_sp : PreAdicSpace.{u}} (CZ : CompleteAffinoidOpen Z_sp)
    (CY : CompleteAffinoidOpen Y_sp) (CX : CompleteAffinoidOpen X_sp) [IsHuberStandard CZ.Ring]
    {TC : Finset CX.Ring} {sC : CX.Ring}
    (hTC : IsOpen (Ideal.span (TC : Set CX.Ring) : Set CX.Ring))
    {ψ : Pair.Hom CZ.pair CY.pair} (hψ : ψ.IsTopologicallyFiniteType)
    {χ : Pair.Hom CZ.pair CX.pair} (hχ : χ.IsTopologicallyFiniteType)
    (hχ_fp : DiscreteTopology CZ.Ring → χ.toRingHom.FinitePresentation)
    {φ : Pair.Hom CY.pair (CX.rationalShrink TC sC hTC).pair} (hφ : φ.IsTopologicallyFiniteType)
    (hφψ : φ.comp ψ = (CX.toRationalShrinkHom TC sC hTC).comp χ) :
    DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation := fun _ ↦ by
  rcases IsHuberStandard.discreteTopology_or_isNoetherianRing_of_isTopologicallyFiniteType
      hψ.isTopologicallyFiniteType_toRingHom with hDiscA | _
  · have : DiscreteTopology CX.Ring := hχ.isTopologicallyFiniteType_toRingHom.discreteTopology
    have hcomp : (φ.toRingHom.comp ψ.toRingHom).FinitePresentation := by
      rw [← Pair.Hom.toRingHom_comp, hφψ, Pair.Hom.toRingHom_comp]
      exact (finitePresentation_toRationalLocalizationHom CX.pod CX.le_plus CX.isSheaf CX.hom TC sC
        hTC).comp (hχ_fp hDiscA)
    exact RingHom.FinitePresentation.of_comp_finiteType ψ.toRingHom hcomp
      hψ.isTopologicallyFiniteType_toRingHom.finiteType
  · have : DiscreteTopology (CX.rationalShrink TC sC hTC).Ring :=
      hφ.isTopologicallyFiniteType_toRingHom.discreteTopology
    exact RingHom.FinitePresentation.of_finiteType.mp
      hφ.isTopologicallyFiniteType_toRingHom.finiteType

theorem LocallyOfFinitePresentation.exists_openImmersion_over_rationalLocalization {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (CY : CompleteAffinoidOpen Y.obj) (x : X.obj)
    {a₀ : CY.space} (ha₀ : CY.hom.base a₀ = f.hom.base x) :
    ∃ (TA : Finset CY.Ring) (sA : CY.Ring)
      (hTA : IsOpen (Ideal.span (TA : Set CY.Ring) : Set CY.Ring)),
      a₀ ∈ spaBasicOpen CY.pair.plus TA sA ∧
      let CY₁ := CY.rationalShrink TA sA hTA
      IsHuberStandard CY₁.Ring ∧
      ∃ (CX : CompleteAffinoidOpen X.obj) (β : Pair.Hom CY₁.pair CX.pair)
        (_ : β.IsTopologicallyFiniteType)
        (_ : DiscreteTopology CY₁.Ring → β.toRingHom.FinitePresentation) (c₀ : CX.space),
        CX.hom.base c₀ = x ∧ CY₁.pairComap CX β ≫ CY₁.hom = CX.hom ≫ f.hom := by
  obtain ⟨CY', CX₀, _, φ', hφ', hfp', c₀₀, hc₀₀, hsq'⟩ := hf.exists_openImmersion_chart x
  have had₀ : (CY'.hom ≫ 𝟙 Y.obj).base ((CY'.pairComap CX₀ φ').base c₀₀) = CY.hom.base a₀ := by
    simpa [hc₀₀, ha₀] using congrArg (fun m ↦ m.base c₀₀) hsq'
  obtain ⟨TA', sA', hTA', -, a'₁, α₀, ha'₁, hsq_α₀⟩ :=
    exists_ofRationalLocalization_lift CY'.pod CY'.le_plus CY'.isSheaf CY'.hom CY (𝟙 Y.obj) had₀
  let CY'₁ := CY'.rationalShrink TA' sA' hTA'
  have had₁ : (CY.hom ≫ 𝟙 Y.obj).base a₀ = CY'₁.hom.base a'₁ := by
    dsimp only [CY'₁, rationalShrink]; rw [Category.comp_id, ha'₁]; simpa using had₀.symm
  obtain ⟨TA, sA, hTA, ha₀R, a₁, α₁, ha₁, hsq_α₁⟩ :=
    exists_ofRationalLocalization_lift CY.pod CY.le_plus CY.isSheaf CY.hom CY'₁ (𝟙 Y.obj) had₁
  refine ⟨TA, sA, hTA, ha₀R, ?_⟩
  let CY₁ := CY.rationalShrink TA sA hTA
  have hα₁α₀ : α₁.comp α₀ = CY.toRationalShrinkHom TA sA hTA := by
    have hl : CY'₁.pairComap CY₁ α₁ ≫ CY.pairComap CY'₁ α₀ =
        toRationalLocalizationComap CY.pod CY.le_plus CY.isSheaf CY.hom TA sA hTA := by
      rw [← cancel_mono CY.hom, Category.assoc, hsq_α₀, Category.comp_id, hsq_α₁, Category.comp_id,
        ofRationalLocalization_hom]
    have h := congrArg (presentationLimitHomPairHom CY.pod CY₁.pod CY.pair CY₁.pair CY.le_plus
      CY₁.le_plus) hl
    rwa [← presentationLimitPreAdicSpacePairComap_comp CY.pod CY'₁.pod CY₁.pod CY.le_plus
        CY'₁.le_plus CY₁.le_plus CY'₁.isSheaf CY₁.isSheaf,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap CY.pod CY₁.pod CY.pair
        CY₁.pair CY.le_plus CY₁.le_plus CY₁.isSheaf,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap CY.pod CY₁.pod CY.pair
        CY₁.pair CY.le_plus CY₁.le_plus CY₁.isSheaf] at h
  have hα₁_tft : α₁.IsTopologicallyFiniteType := .of_comp (by
    rw [hα₁α₀]
    exact isTopologicallyFiniteType_toRationalLocalizationHom CY.pod CY.le_plus CY.isSheaf CY.hom TA
      sA hTA)
  let ψ₀ := α₁.comp (CY'.toRationalShrinkHom TA' sA' hTA')
  have hψ₀_tft := hα₁_tft.comp (isTopologicallyFiniteType_toRationalLocalizationHom CY'.pod
    CY'.le_plus CY'.isSheaf CY'.hom TA' sA' hTA')
  refine ⟨.of_isTopologicallyFiniteType hψ₀_tft.isTopologicallyFiniteType_toRingHom, ?_⟩
  have hsq_ψ₀ : CY'.pairComap CY₁ ψ₀ ≫ CY'.hom = CY₁.hom ≫ 𝟙 Y.obj := by
    rw [pairComap, presentationLimitPreAdicSpacePairComap_comp CY'.pod CY'₁.pod CY₁.pod CY'.le_plus
      CY'₁.le_plus CY₁.le_plus CY'₁.isSheaf CY₁.isSheaf, Category.assoc]
    have h := hsq_α₁; dsimp only [CY'₁, rationalShrink] at h
    rw [ofRationalLocalization_hom] at h; exact h
  obtain ⟨TC, sC, hTC, β, hβ_tft, c₁, hc₁, hsq, hβψ₀⟩ :=
    exists_rational_shrink_lift_sq (f_hom := f.hom) (g_hom := 𝟙 Y.obj) CY' CY₁ CX₀.pod CX₀.le_plus
      CX₀.isSheaf CX₀.hom ψ₀ φ' hφ' (ha₁.trans ha₀) hc₀₀ hsq_ψ₀ (by simpa using hsq')
  exact ⟨CX₀.rationalShrink TC sC hTC, β, hβ_tft,
    finitePresentation_of_comp_eq_toRationalShrinkHom_comp CY' CY₁ CX₀ hTC hψ₀_tft hφ' hfp' hβ_tft
      hβψ₀,
    c₁, hc₁, hsq⟩

/-- **Composition of morphisms locally of finite presentation** (Huber 1996, §1.2). -/
theorem LocallyOfFinitePresentation.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyOfFinitePresentation f) (hg : LocallyOfFinitePresentation g) :
    LocallyOfFinitePresentation (f ≫ g) := fun x ↦ by
  obtain ⟨CZ, CY, _, ψ, hψ, hψ_fp, b₀, hb₀, hsq_g⟩ :=
    hg.exists_openImmersion_chart (f.hom.base x)
  obtain ⟨TB, sB, hTB, -, -, CX, β, hβ, hβ_fp, c₀, hc₀, hsq_f⟩ :=
    hf.exists_openImmersion_over_rationalLocalization CY x hb₀
  let CY₁ := CY.rationalShrink TB sB hTB
  let ψ₁ := (CY.toRationalShrinkHom TB sB hTB).comp ψ
  have hψ₁_tft := (isTopologicallyFiniteType_toRationalLocalizationHom CY.pod CY.le_plus CY.isSheaf
    CY.hom TB sB hTB).comp hψ
  let χ := β.comp ψ₁
  have hχ_fp : DiscreteTopology CZ.Ring → χ.toRingHom.FinitePresentation := fun hDiscA ↦ by
    have : DiscreteTopology CY.Ring := hψ.isTopologicallyFiniteType_toRingHom.discreteTopology
    have : DiscreteTopology CY₁.Ring := hψ₁_tft.isTopologicallyFiniteType_toRingHom.discreteTopology
    rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp]
    exact (hβ_fp inferInstance).comp
      ((finitePresentation_toRationalLocalizationHom CY.pod CY.le_plus CY.isSheaf CY.hom TB sB
        hTB).comp (hψ_fp hDiscA))
  refine exists_locallyOfFinitePresentation_chart_of_openImmersion_sq CZ CX χ (hβ.comp hψ₁_tft)
    hχ_fp hc₀ ?_
  rw [pairComap, presentationLimitPreAdicSpacePairComap_comp CZ.pod CY₁.pod CX.pod CZ.le_plus
      CY₁.le_plus CX.le_plus CY₁.isSheaf CX.isSheaf,
    presentationLimitPreAdicSpacePairComap_comp CZ.pod CY.pod CY₁.pod CZ.le_plus CY.le_plus
      CY₁.le_plus CY.isSheaf CY₁.isSheaf,
    Category.assoc, Category.assoc, hsq_g, ← Category.assoc _ CY.hom,
    ← ofRationalLocalization_hom, ← Category.assoc, hsq_f, Category.assoc,
    ObjectProperty.FullSubcategory.comp_hom]

instance LocallyOfFinitePresentation.isStableUnderComposition :
    LocallyOfFinitePresentation.{u}.IsStableUnderComposition where
  comp_mem _ _ hf hg := hf.comp hg

end TauCeti.AdicSpace
