/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Affinoid
public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.PlusWeaklyFiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Open
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Discrete

import Mathlib.RingTheory.RingHom.FiniteType
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.CompleteChart
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Morphisms of adic spaces locally of finite type

A morphism `f : X ⟶ Y` of adic spaces is *locally of finite type* (Huber 1996, Definition
1.2.1(iii); Huber 1994, §3, p. 535; Wedhorn, Definition 8.42 and Definition 8.48) when its
underlying morphism of pre-adic spaces is locally of finite type: every point `x` of `X` has an
open neighbourhood `U`, mapped by `f` into an open `V` of `Y`, together with Huber pairs `(A, A⁺)`
and `(B, B⁺)` with `B` complete and Hausdorff, a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)`
topologically of finite type (`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType`), and isomorphisms
identifying `X|_U` with `Spa(B, B⁺)` and `Y|_V` with `Spa(A, A⁺)` under which `f` corresponds to
the morphism induced by `φ`.

Using the `CompleteAffinoidOpen` chart machinery from `PreAdicSpace.Affinoid.Open`, this file
develops the chart-refinement API for `LocallyOfFiniteType`, proves Wedhorn's Proposition 8.50
(closure under composition, right-cancellation, and restriction along open immersions), gives the
affinoid criterion for arbitrary (not necessarily complete) Huber pairs, and proves the discrete
affinoid comparison `LocallyOfFiniteType (comapOfPair hS hT φ) ↔ φ.toRingHom.FiniteType`.

## Main definitions

* `TauCeti.AdicSpace.LocallyOfFiniteType`: the `MorphismProperty` of morphisms of adic spaces
  locally of finite type.

## Main results

* `TauCeti.AdicSpace.LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.locallyOfWeaklyFiniteType`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.isAdic`: implications down Huber's hierarchy.
* `TauCeti.AdicSpace.LocallyOfFiniteType.exists_complete_openImmersion_chart`,
  `TauCeti.AdicSpace.locallyOfFiniteType_of_forall_openImmersion_sq`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.exists_openImmersion_over_rationalLocalization`:
  open-immersion chart extraction, construction, and refinement over rational localisations.
* `TauCeti.AdicSpace.LocallyOfFiniteType.comp`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.isMultiplicative`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.of_comp`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.restrict`: Wedhorn, Proposition 8.50.
* `TauCeti.AdicSpace.locallyOfFiniteType_comapOfPresentation`,
  `TauCeti.AdicSpace.locallyOfFiniteType_comapOfPair`: affinoid morphisms induced by Huber-pair
  morphisms topologically of finite type are locally of finite type.
* `TauCeti.AdicSpace.LocallyOfFiniteType.finiteType_of_discreteTopology`,
  `TauCeti.AdicSpace.locallyOfFiniteType_comapOfPair_discrete_iff`: discrete affinoid comparison
  with algebraic `RingHom.FiniteType`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3, p. 535.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), Definition 1.2.1(iii).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 8.42, Definition
  8.48, and Proposition 8.50.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace AdicSpace

open PreAdicSpace

/-- **Morphisms locally of finite type** (Huber 1996, Definition 1.2.1(iii); Huber 1994, §3,
p. 535; Wedhorn, Definition 8.42 and Definition 8.48): a morphism `f : X ⟶ Y` of adic spaces is
*locally of finite type* when every point `x` of `X` has an open neighbourhood `U`, mapped by `f`
into an open `V` of `Y`, together with Huber pairs `(A, A⁺)` and `(B, B⁺)` with `B` complete and
Hausdorff, a morphism `φ : (A, A⁺) → (B, B⁺)` topologically of finite type, and isomorphisms
`X|_U ≅ Spa(B, B⁺)` and `Y|_V ≅ Spa(A, A⁺)` under which `f` corresponds to the morphism induced by
`φ`. Equivalently, `f.hom` satisfies `TauCeti.PreAdicSpace.LocallyOfFiniteType`. -/
def LocallyOfFiniteType : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  PreAdicSpace.LocallyOfFiniteType f.hom

variable {X Y Z : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.LocallyOfFiniteType` in terms of
`TauCeti.PreAdicSpace.LocallyOfFiniteType`. -/
theorem locallyOfFiniteType_iff (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ PreAdicSpace.LocallyOfFiniteType f.hom := Iff.rfl

/-- Unfolding lemma for `TauCeti.AdicSpace.LocallyOfFiniteType` in terms of
`TauCeti.PreAdicSpace.chartLocally`. -/
theorem locallyOfFiniteType_iff_chartLocally (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ chartLocally (fun φ ↦ φ.IsTopologicallyFiniteType) f.hom :=
  PreAdicSpace.locallyOfFiniteType_iff f.hom

/-- **A morphism of adic spaces locally of finite type is locally of +weakly finite type**
(Huber 1996, §1.2): a morphism of Huber pairs topologically of finite type is of +weakly finite
type. -/
theorem LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) : LocallyOfPlusWeaklyFiniteType f :=
  (locallyOfPlusWeaklyFiniteType_iff_chartLocally f).mpr <|
    chartLocally_mono (fun _ hφ ↦ hφ.isPlusWeaklyFiniteType)
      ((locallyOfFiniteType_iff_chartLocally f).mp hf)

/-- **A morphism of adic spaces locally of finite type is locally of weakly finite type**
(Huber 1996, §1.2; Wedhorn, Definition 8.48). -/
theorem LocallyOfFiniteType.locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) : LocallyOfWeaklyFiniteType f :=
  hf.locallyOfPlusWeaklyFiniteType.locallyOfWeaklyFiniteType

/-- **A morphism of adic spaces locally of finite type is adic** (Huber 1996, §1.2). -/
theorem LocallyOfFiniteType.isAdic {f : X ⟶ Y} (hf : LocallyOfFiniteType f) : IsAdic f :=
  hf.locallyOfWeaklyFiniteType.isAdic

/-- **Identities on adic spaces are locally of finite type.** -/
instance LocallyOfFiniteType.containsIdentities :
    LocallyOfFiniteType.{u}.ContainsIdentities where id_mem X := locallyOfFiniteType_id X.property

/-- **Being locally of finite type is invariant under isomorphisms** of the source and of the
target. -/
instance LocallyOfFiniteType.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
  MorphismProperty.RespectsIso.inverseImage
    (@PreAdicSpace.LocallyOfFiniteType.{u}) (ObjectProperty.ι PreAdicSpace.isAdic)

/-- **Open immersions of adic spaces are locally of finite type.** -/
theorem LocallyOfFiniteType.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] : LocallyOfFiniteType f :=
  locallyOfFiniteType_of_isOpenImmersion f.hom X.property

/-- **Every morphism out of an empty adic space is locally of finite type.** -/
theorem LocallyOfFiniteType.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] : LocallyOfFiniteType f :=
  (locallyOfFiniteType_iff_chartLocally f).mpr <| (chartLocally_iff _).mpr fun x ↦ isEmptyElim x

section OpenImmersionCharts

open CompleteAffinoidOpen

/-- **Open-immersion chart extraction for `LocallyOfFiniteType`**: if `f : X ⟶ Y` is locally of
finite type, then every point `x ∈ X` admits complete Hausdorff sheafy affinoid opens `CY` of `Y`
and `CX` of `X` with `x` in the image of `CX.hom` and a morphism `φ : CY.pair → CX.pair`
topologically of finite type making the open-immersion square commute. -/
theorem LocallyOfFiniteType.exists_complete_openImmersion_chart {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (x : X.obj) :
    ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
      (φ : Pair.Hom CY.pair CX.pair) (_ : φ.IsTopologicallyFiniteType) (b₀ : CX.space),
      CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom := by
  obtain ⟨U, hxU, V, -, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, hsheafB, eU, eV, hfac⟩ :=
    exists_complete_chart_of_chartLocally (fun φ ↦ φ.IsTopologicallyFiniteType)
      (fun h ↦ .of_comp h) ((locallyOfFiniteType_iff_chartLocally f).mp hf) x
  have hsheafA := isSheaf_of_restrict_iso P hP eV
  exact ⟨ofRestrictIso S P hP hsheafA eV, ofRestrictIso T P' hP' hsheafB eU, φ, hφ,
    eU.hom.base ⟨x, hxU⟩, ofRestrictIso_hom_base T P' hP' hsheafB eU hxU,
    ofRestrictIso_pairComap_comp_hom S P hP hsheafA eV T P' hP' hsheafB eU φ hfac⟩

/-- **Open-immersion chart criterion for `LocallyOfFiniteType`**: a morphism `f : X ⟶ Y` of adic
spaces is locally of finite type if every point `x ∈ X` is covered by a complete affinoid
open-immersion square induced by a morphism of Huber pairs topologically of finite type. -/
theorem locallyOfFiniteType_of_forall_openImmersion_sq {f : X ⟶ Y}
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
    exact (ValuationSpectrum.locallyOfFiniteType_presentationLimitPreAdicSpaceComap
      (CY x).pairOfDefinition (CX x).pairOfDefinition (CY x).le_plus (CX x).le_plus
      (CX x).isSheaf (φ x) (hφ x)).comp_of_isOpenImmersion (CY x).hom
  rwa [← heU, Category.assoc,
    MorphismProperty.cancel_left_of_respectsIso @PreAdicSpace.LocallyOfFiniteType.{u}]

/-- **Chart refinement over a prescribed target open for `LocallyOfFiniteType`**: given
`f : X ⟶ Y` locally of finite type, a complete affinoid open `CY` of `Y`, and a point `x ∈ X`
whose image `f(x)` is hit by `a₀ ∈ CY.space`, there is a rational localisation
`CY₁ = CY.rationalLocalization TA sA hTA` containing `a₀` and a complete affinoid open `CX` of `X`
covering `x` over `CY₁` via a Huber-pair morphism `β` topologically of finite type. -/
theorem LocallyOfFiniteType.exists_openImmersion_over_rationalLocalization {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (CY : CompleteAffinoidOpen Y.obj) (x : X.obj)
    {a₀ : CY.space} (ha₀ : CY.hom.base a₀ = f.hom.base x) : ∃ (TA : Finset CY.Ring) (sA : CY.Ring)
      (hTA : IsOpen (Ideal.span (TA : Set CY.Ring) : Set CY.Ring)),
      a₀ ∈ spaBasicOpen CY.pair.plus TA sA ∧
      let CY₁ := CY.rationalLocalization TA sA hTA
      ∃ (CX : CompleteAffinoidOpen X.obj) (β : Pair.Hom CY₁.pair CX.pair)
        (_ : β.IsTopologicallyFiniteType) (c₀ : CX.space),
        CX.hom.base c₀ = x ∧ CY₁.pairComap CX β ≫ CY₁.hom = CX.hom ≫ f.hom := by
  obtain ⟨CY', CX₀, φ', hφ', c₀₀, hc₀₀, hsq'⟩ := hf.exists_complete_openImmersion_chart x
  have had : (CY.hom ≫ 𝟙 Y.obj).base a₀ = CY'.hom.base ((CY'.pairComap CX₀ φ').base c₀₀) := by
    rw [Category.comp_id, ha₀, ← hc₀₀, ← CY'.pairComap_comp_hom_base CX₀ φ' hsq' c₀₀]
  obtain ⟨TA, sA, hTA, ha₀R, a₁, α₁, ha₁, hsq_α⟩ :=
    exists_ofRationalLocalization_lift CY.pairOfDefinition CY.le_plus CY.isSheaf CY.hom
      CY' (𝟙 Y.obj) had
  obtain ⟨TC, sC, hTC, β, c₁, hc₁, hsq, hβα⟩ :=
    exists_rationalLocalization_lift_sq (f := f.hom) (g := 𝟙 Y.obj) CY'
      (CY.rationalLocalization TA sA hTA) CX₀ α₁ φ' (ha₁.trans ha₀) hc₀₀ hsq_α (by simpa using hsq')
  exact ⟨TA, sA, hTA, ha₀R, CX₀.rationalLocalization TC sC hTC, β,
    .of_comp (hβα ▸ (CX₀.isTopologicallyFiniteType_rationalLocalizationHom TC sC hTC).comp hφ'),
    c₁, hc₁, hsq⟩

/-- **Composition of morphisms locally of finite type** (Wedhorn, Proposition 8.50(1)): if
`f : X ⟶ Y` and `g : Y ⟶ Z` are locally of finite type, then `f ≫ g` is locally of finite type.
-/
theorem LocallyOfFiniteType.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyOfFiniteType f) (hg : LocallyOfFiniteType g) : LocallyOfFiniteType (f ≫ g) := by
  refine locallyOfFiniteType_of_forall_openImmersion_sq fun x ↦ ?_
  obtain ⟨CZ, CY, ψ, hψ, b₀, hb₀, hsq_g⟩ := hg.exists_complete_openImmersion_chart (f.hom.base x)
  obtain ⟨TB, sB, hTB, -, CX, β, hβ, c₀, hc₀, hsq_f⟩ :=
    hf.exists_openImmersion_over_rationalLocalization CY x hb₀
  exact ⟨CZ, CX, β.comp ((CY.rationalLocalizationHom TB sB hTB).comp ψ),
    hβ.comp ((CY.isTopologicallyFiniteType_rationalLocalizationHom TB sB hTB).comp hψ), c₀, hc₀, by
      rw [ObjectProperty.FullSubcategory.comp_hom]
      exact CZ.pairComap_comp_rationalLocalization_sq CY hTB CX ψ β hsq_g hsq_f⟩

/-- `LocallyOfFiniteType` is stable under composition. -/
instance LocallyOfFiniteType.isStableUnderComposition :
    LocallyOfFiniteType.{u}.IsStableUnderComposition where comp_mem _ _ hf hg := hf.comp hg

/-- `LocallyOfFiniteType` is multiplicative (contains identities and is stable under
composition). -/
instance LocallyOfFiniteType.isMultiplicative :
    LocallyOfFiniteType.{u}.IsMultiplicative where

/-- **Right-cancellation of morphisms locally of finite type** (Wedhorn, Proposition 8.50(2)): if
`f ≫ g` is locally of finite type, then `f` is locally of finite type. -/
theorem LocallyOfFiniteType.of_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : LocallyOfFiniteType (f ≫ g)) : LocallyOfFiniteType f := by
  classical
  refine locallyOfFiniteType_of_forall_openImmersion_sq fun x ↦ ?_
  obtain ⟨CZ, CX, χ, hχ, c₀, hc₀, hsq_fg⟩ := hfg.exists_complete_openImmersion_chart x
  let OY : Opens Y.obj := ⟨g.hom.base ⁻¹' Set.range CZ.hom.base,
    CZ.hom.isOpenEmbedding.isOpen_range.preimage g.hom.base.hom.continuous_toFun⟩
  have hfxO : f.hom.base x ∈ OY := by
    refine ⟨(CZ.pairComap CX χ).base c₀, ?_⟩
    have h := CZ.pairComap_comp_hom_base CX χ hsq_fg c₀
    rwa [ObjectProperty.FullSubcategory.comp_hom, PreAdicSpace.comp_base, TopCat.coe_comp,
      Function.comp_apply, hc₀] at h
  obtain ⟨W, hW, hfxW, hWO⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affinoidOpens Y.property.isLocallyAffinoid) hfxO
  obtain ⟨B, _, _, _, _, _, _, _, T, P', hP', hsheafB, ⟨eW⟩⟩ :=
    Y.property.isSheafy.exists_complete_isSheaf_of_mem_affinoidOpens hW
  let CY := ofRestrictIso T P' hP' hsheafB eW
  have hb₀ : CY.hom.base (eW.hom.base ⟨f.hom.base x, hfxW⟩) = f.hom.base x :=
    ofRestrictIso_hom_base T P' hP' hsheafB eW hfxW
  have hrangeY : Set.range (CY.hom ≫ g.hom).base ⊆ Set.range CZ.hom.base := by
    rintro _ ⟨b, rfl⟩
    rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply,
      ofRestrictIso_hom_base_apply T P' hP' hsheafB eW b]
    exact hWO (eW.inv.base b).property
  let p := PreAdicSpace.IsOpenImmersion.lift CZ.hom (CY.hom ≫ g.hom) hrangeY
  let ψ := presentationLimitHomPairHom CZ.pairOfDefinition CY.pairOfDefinition CZ.pair CY.pair
    CZ.le_plus CY.le_plus p
  have hsq_g : CZ.pairComap CY ψ ≫ CZ.hom = CY.hom ≫ g.hom := by
    rw [pairComap, presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom
      CZ.pairOfDefinition CY.pairOfDefinition CZ.pair CY.pair CZ.le_plus CY.le_plus CY.isSheaf]
    exact PreAdicSpace.IsOpenImmersion.lift_fac CZ.hom (CY.hom ≫ g.hom) hrangeY
  obtain ⟨TC, sC, hTC, φ, c₁, hc₁, hsq_f, hφψ⟩ :=
    exists_rationalLocalization_lift_sq (f := f.hom) (g := g.hom) CZ CY CX ψ χ hb₀ hc₀ hsq_g hsq_fg
  exact ⟨CY, CX.rationalLocalization TC sC hTC, φ,
    .of_comp (hφψ ▸ (CX.isTopologicallyFiniteType_rationalLocalizationHom TC sC hTC).comp hχ),
    c₁, hc₁, hsq_f⟩

/-- **Restriction of `LocallyOfFiniteType` along an open immersion of the source** (Wedhorn,
Proposition 8.50(3)): given a commuting square `g ≫ iV = iU ≫ f` of adic spaces with `iU` an open
immersion and `f` locally of finite type, the morphism `g` is locally of finite type. -/
theorem LocallyOfFiniteType.restrict {U V : AdicSpace.{u}} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} {g : U ⟶ V} [PreAdicSpace.IsOpenImmersion iU.hom]
    (hcomm : g ≫ iV = iU ≫ f) (hf : LocallyOfFiniteType f) : LocallyOfFiniteType g :=
  LocallyOfFiniteType.of_comp (g := iV)
    (hcomm ▸ (LocallyOfFiniteType.of_isOpenImmersion iU).comp hf)

end OpenImmersionCharts

section Affinoid

open CompleteAffinoidOpen

/-- **Affinoid morphisms (presentation level)**: if `φ : S → T` is a morphism of Huber pairs
topologically of finite type between sheafy presentations, then the induced morphism
`comapOfPresentation S P hS hsheafS T P' hT hsheafT φ` of affinoid adic spaces is locally of
finite type. No completeness or Hausdorff assumption on `A` or `B` is needed. -/
theorem locallyOfFiniteType_comapOfPresentation {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B]
    (S : Pair A) (P : PairOfDefinition A) (hS : P.ringOfDefinition ≤ S.plus)
    (hsheafS : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (T : Pair B) (P' : PairOfDefinition B) (hT : P'.ringOfDefinition ≤ T.plus)
    (hsheafT : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus)) (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFiniteType (comapOfPresentation S P hS hsheafS T P' hT hsheafT φ) := by
  refine locallyOfFiniteType_of_forall_openImmersion_sq fun x ↦ ?_
  obtain ⟨b₀, hb₀⟩ : x ∈ Set.range (ofCompletion P' hT hsheafT).hom.base :=
    range_ofCompletion_hom_base P' hT hsheafT ▸ Set.mem_univ _
  refine ⟨ofCompletion P hS hsheafS, ofCompletion P' hT hsheafT,
    ofCompletionMap P hS hsheafS P' hT hsheafT φ,
    isTopologicallyFiniteType_ofCompletionMap P hS hsheafS P' hT hsheafT φ hφ, b₀, hb₀, ?_⟩
  rw [comapOfPresentation_hom]
  exact pairComap_ofCompletionMap_comp_hom P hS hsheafS P' hT hsheafT φ

/-- Comparing `LocallyOfFiniteType` on `comapOfPair` with `comapOfPresentation` via the canonical
isomorphisms `ofPairIsoOfPresentation`. -/
theorem locallyOfFiniteType_comapOfPair_iff_comapOfPresentation {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [TopologicalSpace B]
    [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus) (P' : PairOfDefinition B)
    (hP' : P'.ringOfDefinition ≤ T.plus) (φ : Pair.Hom S T) :
    LocallyOfFiniteType (comapOfPair hS hT φ) ↔ LocallyOfFiniteType
        (comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso (@LocallyOfFiniteType.{u}) _
      (ofPairIsoOfPresentation S hS P hP).hom,
    ← ofPairIsoOfPresentation_hom_comapOfPresentation hS hT P hP P' hP' φ,
    MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType.{u})]

/-- **Affinoid morphisms**: if `φ : S → T` is a morphism of Huber pairs topologically of finite
type between pairs whose adic spectra are sheafy for every presentation, then `comapOfPair hS hT φ`
is locally of finite type. -/
theorem locallyOfFiniteType_comapOfPair {A B : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFiniteType (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  exact (locallyOfFiniteType_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mpr
    (locallyOfFiniteType_comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP')
      φ hφ)

/-- **Discrete descent for `LocallyOfFiniteType`**: if `φ : S → T` is a morphism of Huber pairs
with discrete underlying rings and `comapOfPair hS hT φ` is locally of finite type, then the
underlying ring homomorphism `φ.toRingHom` is of finite type (`RingHom.FiniteType`). -/
theorem LocallyOfFiniteType.finiteType_of_discreteTopology {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] {S : Pair A} {T : Pair B}
    {hS : IsSheafyForEveryPresentation S.plus} {hT : IsSheafyForEveryPresentation T.plus}
    {φ : Pair.Hom S T} (hf : LocallyOfFiniteType (comapOfPair hS hT φ)) :
    φ.toRingHom.FiniteType := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  have hq := (locallyOfFiniteType_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mp hf
  let CA := ofDiscrete S P hP (hS.isSheaf P hP)
  refine PreAdicSpace.ringHom_prop_of_forall_rational_chart_discrete
    RingHom.finiteType_stableUnderComposition RingHom.finiteType_respectsIso
    RingHom.finiteType_holdsForLocalizationAway RingHom.finiteType_ofLocalizationSpanTarget
    P hP (hS.isSheaf P hP) P' hP' (hT.isSheaf P' hP') φ fun y ↦ ?_
  obtain ⟨TA, sA, hTA, -, CX, β, hβ, c₀, hc₀, hsq⟩ :=
    hq.exists_openImmersion_over_rationalLocalization CA y rfl
  have : DiscreteTopology (CA.rationalLocalization TA sA hTA).Ring :=
    (CA.isTopologicallyFiniteType_rationalLocalizationHom TA sA
      hTA).isTopologicallyFiniteType_toRingHom.discreteTopology
  obtain ⟨hDiscC, hβ_ft⟩ := isTopologicallyFiniteType_iff_discreteTopology_and_finiteType.mp
    hβ.isTopologicallyFiniteType_toRingHom
  rw [comapOfPresentation_hom] at hsq; exact ⟨TA, sA, hTA, CX, hDiscC, β, hβ_ft, c₀, hc₀, hsq⟩

/-- **Discrete affinoid comparison for `LocallyOfFiniteType`**: for discrete rings `A, B` with
maximal plus subrings `Pair.discrete A` and `Pair.discrete B`, the affinoid morphism
`Spa(B, B) ⟶ Spa(A, A)` induced by `φ` is locally of finite type if and only if the underlying
ring homomorphism `φ.toRingHom : A →+* B` is of finite type (`RingHom.FiniteType`). -/
theorem locallyOfFiniteType_comapOfPair_discrete_iff {A B : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B]
    (hS : IsSheafyForEveryPresentation (Pair.discrete A).plus)
    (hT : IsSheafyForEveryPresentation (Pair.discrete B).plus)
    (φ : Pair.Hom (Pair.discrete A) (Pair.discrete B)) :
    LocallyOfFiniteType (comapOfPair hS hT φ) ↔ φ.toRingHom.FiniteType :=
  ⟨fun hf ↦ hf.finiteType_of_discreteTopology, fun hφ ↦ locallyOfFiniteType_comapOfPair hS hT φ
    ((Pair.Hom.isTopologicallyFiniteType_iff_finiteType_of_plus_eq_top
      Pair.discrete_plus Pair.discrete_plus).mpr hφ)⟩

end Affinoid

end AdicSpace

end TauCeti
