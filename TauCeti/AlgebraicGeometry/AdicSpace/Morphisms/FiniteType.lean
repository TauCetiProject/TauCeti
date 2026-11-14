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

import Mathlib.RingTheory.RingHom.FiniteType
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Complete
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.Discreteness
import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Morphisms of adic spaces locally of finite type

A morphism `f : X ⟶ Y` of adic spaces is *locally of finite type* (Huber 1994, §3; Huber 1996,
Definition 1.2.1(i); Wedhorn, Definition 8.48(1)) when its underlying morphism of pre-adic spaces
is `TauCeti.PreAdicSpace.LocallyOfFiniteType`: every point of `X` has an open neighbourhood `U`,
mapped by `f` into an open `V` of `Y`, such that `U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber
pairs with `B` complete and Hausdorff, under which `f` restricted to `U → V` is induced by a
morphism of Huber pairs `(A, A⁺) → (B, B⁺)` topologically of finite type
(`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType`).

This file packages `TauCeti.AdicSpace.LocallyOfFiniteType` as a `CategoryTheory.MorphismProperty` on
`AdicSpace`, connects it to Huber's finiteness hierarchy (`LocallyOfPlusWeaklyFiniteType`,
`LocallyOfWeaklyFiniteType`, `IsAdic`), and proves Wedhorn's Proposition 8.50 in full generality
over arbitrary Huber bases (with no Tate hypothesis):

* **Composition** (`LocallyOfFiniteType.comp`): composites of morphisms locally of finite type are
  locally of finite type, by refining the source chart over a rational open of an intermediate
  target chart and composing pair morphisms topologically of finite type
  (`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.comp`).
* **Right-cancellation** (`LocallyOfFiniteType.of_comp`): if `f ≫ g` is locally of finite type for
  any morphism `g : Y ⟶ Z` of adic spaces, then `f` is locally of finite type, using pair-level
  cancellation (`TauCeti.Huber.Pair.Hom.IsTopologicallyFiniteType.of_comp`).
* **Restriction to open subspaces** (`LocallyOfFiniteType.restrict`): any morphism fitted into a
  commuting square of open immersions over a morphism locally of finite type is itself locally of
  finite type.
* **Discrete affinoid comparison** (`locallyOfFiniteType_comapOfPair_discrete_iff`): for discrete
  commutative rings `A` and `B` with trivial plus rings `(A, A)` and `(B, B)`, the induced morphism
  `Spa(B, B) ⟶ Spa(A, A)` is locally of finite type if and only if `A →+* B` is algebraically of
  finite type (`RingHom.FiniteType`).

## Main definitions

* `TauCeti.AdicSpace.LocallyOfFiniteType`: morphisms of adic spaces locally of finite type.

## Main results

* `TauCeti.AdicSpace.LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.locallyOfWeaklyFiniteType`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.isAdic`: placement in Huber's finiteness hierarchy.
* `TauCeti.AdicSpace.LocallyOfFiniteType.comp`,
  `TauCeti.AdicSpace.LocallyOfFiniteType.isMultiplicative`: closure under identities and
  composition (Wedhorn, Proposition 8.50(1)).
* `TauCeti.AdicSpace.LocallyOfFiniteType.of_comp`: right-cancellation along arbitrary morphisms of
  adic spaces (Wedhorn, Proposition 8.50(2)).
* `TauCeti.AdicSpace.LocallyOfFiniteType.restrict`: restriction along open immersions of the source.
* `TauCeti.AdicSpace.LocallyOfFiniteType.exists_openImmersion_over_rationalLocalization`: refinement
  of a finite-type morphism over any sheafy affinoid open immersion into the target.
* `TauCeti.AdicSpace.locallyOfFiniteType_comapOfPair_discrete_iff`: over discrete rings with trivial
  plus rings, `LocallyOfFiniteType` agrees with `RingHom.FiniteType`.

## References

* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), §1.2, Definition 1.2.1(i).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definitions 8.42 and 8.48, and
  Propositions 8.46, 8.49, and 8.50.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber Huber.PairOfDefinition PreAdicSpace ValuationSpectrum

universe u

/-- **Morphisms locally of finite type** (Huber 1996, Definition 1.2.1(i); Wedhorn,
Definition 8.48(1)): a morphism `f : X ⟶ Y` of adic spaces is *locally of finite type* when its
underlying morphism of pre-adic spaces is `TauCeti.PreAdicSpace.LocallyOfFiniteType`, i.e. chart-
locally induced by morphisms of Huber pairs topologically of finite type. -/
def LocallyOfFiniteType : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  PreAdicSpace.LocallyOfFiniteType f.hom

variable {X Y Z : AdicSpace.{u}}

/-- Unfolding lemma relating `AdicSpace.LocallyOfFiniteType` to
`PreAdicSpace.LocallyOfFiniteType`. -/
theorem locallyOfFiniteType_iff_preAdicSpace (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ PreAdicSpace.LocallyOfFiniteType f.hom :=
  Iff.rfl

/-- Unfolding lemma relating `AdicSpace.LocallyOfFiniteType` to `PreAdicSpace.chartLocally`. -/
theorem locallyOfFiniteType_iff_chartLocally (f : X ⟶ Y) :
    LocallyOfFiniteType f ↔ chartLocally (fun φ ↦ φ.IsTopologicallyFiniteType) f.hom :=
  locallyOfFiniteType_iff f.hom

/-! ### Hierarchy and ascent of space properties -/

/-- **A morphism locally of finite type is locally of +weakly finite type** (Huber 1996, §1.2). -/
theorem LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) : LocallyOfPlusWeaklyFiniteType f :=
  PreAdicSpace.LocallyOfFiniteType.locallyOfPlusWeaklyFiniteType hf

/-- **A morphism locally of finite type is locally of weakly finite type** (Huber 1996, §1.2). -/
theorem LocallyOfFiniteType.locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) : LocallyOfWeaklyFiniteType f :=
  PreAdicSpace.LocallyOfFiniteType.locallyOfWeaklyFiniteType hf

/-- **A morphism locally of finite type is adic** (Huber 1996, §1.2). -/
theorem LocallyOfFiniteType.isAdic {f : X ⟶ Y} (hf : LocallyOfFiniteType f) : IsAdic f :=
  hf.locallyOfWeaklyFiniteType.isAdic

/-- Locally noetherian structure ascends from the target of a morphism locally of finite type to its
source. -/
theorem LocallyOfFiniteType.isLocallyNoetherian_source {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (hY : Y.IsLocallyNoetherian) : X.IsLocallyNoetherian :=
  hY.of_locallyOfFiniteType hf

/-- Being locally of Huber's standing class ascends from the target of a morphism locally of finite
type to its source. -/
theorem LocallyOfFiniteType.isLocallyHuberStandard_source {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (hY : Y.IsLocallyHuberStandard) : X.IsLocallyHuberStandard :=
  hY.of_locallyOfFiniteType hf

/-! ### Identities, open immersions, isomorphisms, and locality -/

/-- **Identities of adic spaces are locally of finite type** (Wedhorn, Proposition 8.49(1)). -/
instance LocallyOfFiniteType.containsIdentities :
    LocallyOfFiniteType.{u}.ContainsIdentities where
  id_mem X := locallyOfFiniteType_id X.property

/-- **Being locally of finite type is invariant under isomorphisms** of source and target. -/
instance LocallyOfFiniteType.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFiniteType.{u}) :=
  MorphismProperty.RespectsIso.inverseImage
    (@PreAdicSpace.LocallyOfFiniteType.{u}) (ObjectProperty.ι PreAdicSpace.isAdic)

/-- **Open immersions of adic spaces are locally of finite type** (Wedhorn, Proposition 8.49(1)). -/
theorem LocallyOfFiniteType.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] : LocallyOfFiniteType f :=
  locallyOfFiniteType_of_isOpenImmersion f.hom X.property

/-- Every morphism out of an empty adic space is locally of finite type. -/
theorem LocallyOfFiniteType.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] : LocallyOfFiniteType f :=
  (locallyOfFiniteType_iff_chartLocally f).mpr <|
    (chartLocally_iff _).mpr fun x ↦ isEmptyElim x

/-! ### Open-immersion chart refinement, composition, and cancellation -/

section OpenImmersionCharts

-- Upgrade a finite-type chart around `x : X.obj` via `{1} / 1` completion so that both the target
-- and source Huber rings are complete and Hausdorff with sheafy adic spectra, expressed directly as
-- open immersions into `X.obj` and `Y.obj`.
private theorem LocallyOfFiniteType.exists_complete_openImmersion_chart {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) (x : X.obj) :
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (_ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
        (presentationLimitPresheaf P S.plus))
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (hsheafB : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (kX : presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' ⟶ X.obj)
      (_ : PreAdicSpace.IsOpenImmersion kX)
      (kY : presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y.obj)
      (_ : PreAdicSpace.IsOpenImmersion kY)
      (φ : Pair.Hom S T) (_ : φ.IsTopologicallyFiniteType)
      (b₀ : presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
      kX.base b₀ = x ∧
      presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ ≫ kY = kX ≫ f.hom := by
  classical
  obtain ⟨U, hxU, V, -, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheafB, eU, eV, hfac⟩ := (chartLocally_iff f.hom).mp
      ((locallyOfFiniteType_iff_chartLocally f).mp hf) x
  have hT1 : IsOpen (Ideal.span (({1} : Finset A) : Set A) : Set A) := by simp
  let T' : Finset B := ({1} : Finset A).image φ.toRingHom
  let s' : B := φ.toRingHom 1
  have hT1' : IsOpen (Ideal.span (T' : Set B) : Set B) := by simp [T']
  let L := Localization.Away (1 : A)
  let L' := Localization.Away s'
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
  let T₁ := P'.rationalLocalizationPair T hP' T' s' L' hden'
  let P₁' := P'.completionLocalization T' s' L' hden'
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP _ _ L hden
  have hP₁' : P₁'.ringOfDefinition ≤ T₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring T.plus hP' _ _ L' hden'
  have hsheafA := ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy)
  have hsheafA₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S₁.plus))
      (presentationLimitPresheaf P₁ S₁.plus) := by
    rw [rationalLocalizationPair_plus]
    exact isSheaf_presentationLimitPresheaf_completionLocalization P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP _ _ L hden hT1 hsheafA
  have hsheafB₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T₁.plus))
      (presentationLimitPresheaf P₁' T₁.plus) := by
    rw [rationalLocalizationPair_plus]
    exact isSheaf_presentationLimitPresheaf_completionLocalization P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP' _ _ L' hden' hT1' hsheafB
  let φ₁ := P.completionLocPairMap S hP ({1} : Finset A) 1 L hden P' T hP' φ T' s' L' hden' rfl
    (fun _ ht ↦ Finset.mem_image_of_mem _ ht)
  have hφ₁ : φ₁.IsTopologicallyFiniteType :=
    P.isTopologicallyFiniteType_completionLocPairMap S hP ({1} : Finset A) 1 L hden P' T hP' φ T'
      s' L' hden' rfl (fun _ ht ↦ Finset.mem_image_of_mem _ ht) hφ
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hT1')
  obtain ⟨eA, heA⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P hP
      ({1} : Finset A) 1 L hden hT1 (fun y ↦ by rw [rationalSubset_singleton_one]; exact y.2)
      hsheafA₁
  obtain ⟨eB, heB⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P' hP' T' s' L'
      hden' hT1' (fun y ↦ by
        simp only [T', s', Finset.image_singleton, map_one, rationalSubset_singleton_one]
        exact y.2) hsheafB₁
  have hcomm := presentationLimitPreAdicSpaceComap_completionLocPairMap_comp P P' hP hP' φ
    hsheafB ({1} : Finset A) 1 L hden L' hden' hsheafA₁ hsheafB₁
  let kX := eB.hom ≫ eU.inv ≫ X.obj.ofRestrict U.isOpenEmbedding
  let kY := eA.hom ≫ eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding
  have hkX : PreAdicSpace.IsOpenImmersion kX :=
    PreAdicSpace.IsOpenImmersion.comp eB.hom (eU.inv ≫ X.obj.ofRestrict U.isOpenEmbedding)
  have hkY : PreAdicSpace.IsOpenImmersion kY :=
    PreAdicSpace.IsOpenImmersion.comp eA.hom (eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding)
  let b₀ := eB.inv.base (eU.hom.base ⟨x, hxU⟩)
  refine ⟨UniformSpace.Completion L, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S₁, P₁, hP₁, hsheafA₁,
    UniformSpace.Completion L', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T₁, P₁', hP₁', hsheafB₁,
    kX, hkX, kY, hkY, φ₁, hφ₁, b₀, ?_, ?_⟩
  · have hb : (eU.hom ≫ eB.inv ≫ eB.hom ≫ eU.inv).base ⟨x, hxU⟩ = ⟨x, hxU⟩ := by
      simp
      rfl
    exact congrArg (X.obj.ofRestrict U.isOpenEmbedding).base hb
  · dsimp only [kX, kY, T', s', φ₁]
    rw [presentationLimitPreAdicSpacePairComap_def, Category.assoc, Category.assoc, hfac,
      Iso.inv_hom_id_assoc]
    rw [← Category.assoc _ eA.hom, heA, heB, hcomm, Category.assoc]

-- Turn an open-immersion square `Spa(φ) ≫ kY = kX ≫ f` covering `x` into a `chartLocally` witness
-- at `x`.
private theorem exists_chart_of_openImmersion_sq
    {Q : ∀ {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
      {B : Type u} [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B]
      {S : Pair A} {T : Pair B}, Pair.Hom S T → Prop}
    {X Y : PreAdicSpace.{u}} {f : X ⟶ Y} {x : X}
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A]
    {S : Pair A} {P : PairOfDefinition A} (hP : P.ringOfDefinition ≤ S.plus)
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B]
    {T : Pair B} {P' : PairOfDefinition B} (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (kX : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP' ⟶ X)
    [PreAdicSpace.IsOpenImmersion kX]
    (kY : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y)
    [PreAdicSpace.IsOpenImmersion kY]
    (φ : Pair.Hom S T) (hφ : Q φ)
    {b₀ : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP'}
    (hb₀ : kX.base b₀ = x)
    (hsq : presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫ kY = kX ≫ f) :
    ∃ (U : Opens X) (_ : x ∈ U) (V : Opens Y) (_ : U ≤ (Opens.map f.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : IsTopologicalRing A)
      (_ : IsHuberRing A) (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : Q φ)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (eU : X.restrict U.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
          hP')
      (eV : Y.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP),
      X.ofRestrict _ ≫ f =
        eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
          Y.ofRestrict _ := by
  let U : Opens X := ⟨Set.range kX.base, kX.isOpenEmbedding.isOpen_range⟩
  let V : Opens Y := ⟨Set.range kY.base, kY.isOpenEmbedding.isOpen_range⟩
  have hUV : U ≤ (Opens.map f.base).obj V := by
    rintro _ ⟨b, rfl⟩
    refine ⟨(presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ).base b, ?_⟩
    exact congrArg (fun m ↦ m.base b) hsq
  let eU := PreAdicSpace.IsOpenImmersion.isoOfRangeEq (X.ofRestrict U.isOpenEmbedding) kX
    (Opens.set_range_inclusion' U)
  let eV := PreAdicSpace.IsOpenImmersion.isoOfRangeEq (Y.ofRestrict V.isOpenEmbedding) kY
    (Opens.set_range_inclusion' V)
  have heU : eU.hom ≫ kX = X.ofRestrict U.isOpenEmbedding :=
    PreAdicSpace.IsOpenImmersion.isoOfRangeEq_hom_comp _ _ _
  have heV : eV.inv ≫ Y.ofRestrict V.isOpenEmbedding = kY :=
    PreAdicSpace.IsOpenImmersion.isoOfRangeEq_inv_comp _ _ _
  refine ⟨U, ⟨b₀, hb₀⟩, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance,
    S, P, hP, B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, T, P', hP', φ, hφ, hsheaf, eU, eV, ?_⟩
  rw [← presentationLimitPreAdicSpacePairComap_def, heV,
    ← Category.assoc eU.hom, Category.assoc eU.hom, hsq, ← Category.assoc, heU]

/-- **Refinement of a finite-type morphism over a given target affinoid**: let `f : X ⟶ Y` be
locally of finite type, let `kY : Spa(A, A⁺) ⟶ Y.obj` be an open immersion from a Huber pair with
sheafy structure presheaf, and let `x : X.obj` satisfy `f.hom.base x = kY.base a₀`. Then `a₀` has a
rational open neighbourhood `R(TA / sA)` in `Spa(A, A⁺)` and `x` has a complete Hausdorff sheafy
affinoid open neighbourhood `kX : Spa(C, C⁺) ⟶ X.obj` such that `kX ≫ f.hom` factors through
`R(TA / sA)` via a morphism of Huber pairs `β : (A⟨TA / sA⟩, A₁⁺) → (C, C⁺)` topologically of finite
type. -/
theorem LocallyOfFiniteType.exists_openImmersion_over_rationalLocalization {f : X ⟶ Y}
    (hf : LocallyOfFiniteType f) {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {S : Pair A}
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus))
    (kY : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y.obj)
    [PreAdicSpace.IsOpenImmersion kY]
    (x : X.obj)
    {a₀ : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP}
    (ha₀ : kY.base a₀ = f.hom.base x) :
    ∃ (TA : Finset A) (sA : A) (hTA : IsOpen (Ideal.span (TA : Set A) : Set A)),
      a₀ ∈ spaBasicOpen S.plus TA sA ∧
      letI LA := Localization.Away sA
      letI hdenA := P.hasDenominatorPower_of_isOpen_span TA sA LA hTA
      letI := P.locUniformSpace TA sA LA hdenA
      letI := P.isUniformAddGroup_locUniformSpace TA sA LA hdenA
      letI := P.isTopologicalRing_locUniformSpace TA sA LA hdenA
      letI := P.isHuberRing_completion_locTopology TA sA LA hdenA
      letI S₁ := P.rationalLocalizationPair S hP TA sA LA hdenA
      letI P₁ := P.completionLocalization TA sA LA hdenA
      haveI hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
        rw [rationalLocalizationPair_plus]
        exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP TA sA LA
          hdenA
      haveI hsheafA₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S₁.plus))
          (presentationLimitPresheaf P₁ S₁.plus) :=
        isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP TA sA LA hdenA hTA hsheafA
      ∃ (C : Type u) (_ : CommRing C) (_ : UniformSpace C) (_ : IsUniformAddGroup C)
        (_ : IsTopologicalRing C) (_ : CompleteSpace C) (_ : T2Space C) (_ : IsHuberRing C)
        (U : Pair C) (PC : PairOfDefinition C) (hPC : PC.ringOfDefinition ≤ U.plus)
        (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
          (presentationLimitPresheaf PC U.plus))
        (kX : presentationLimitPreAdicSpace PC U.plus
          U.isRingOfIntegralElements.isPowerBounded_of_mem hPC ⟶ X.obj)
        (_ : PreAdicSpace.IsOpenImmersion kX)
        (β : Pair.Hom S₁ U) (_ : β.IsTopologicallyFiniteType)
        (c₀ : presentationLimitPreAdicSpace PC U.plus
          U.isRingOfIntegralElements.isPowerBounded_of_mem hPC),
        kX.base c₀ = x ∧
        presentationLimitPreAdicSpacePairComap P₁ PC hP₁ hPC hsheafC β ≫
          presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
            (P.toCompletionLocHom S hP TA sA LA hdenA) ≫ kY = kX ≫ f.hom := by
  classical
  -- 1. Choose a complete FT chart `(kX₀ : Spa(C₀) ⟶ X, kY' : Spa(A') ⟶ Y, φ' : A' → C₀)`.
  obtain ⟨A', _, _, _, _, _, _, _, S', P', hP', -, C₀, _, _, _, _, _, _, _, U₀, PC₀, hPC₀,
    hsheafC₀, kX₀, hkX₀, kY', hkY', φ', hφ', c₀₀, hc₀₀, hsq'⟩ :=
    hf.exists_complete_openImmersion_chart x
  -- 2. Shrink `Spa(A, A⁺)` around `a₀` to a rational open `R(TA / sA)` landing in `Set.range kY'`.
  let OA : Opens (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
    ⟨kY.base ⁻¹' Set.range kY'.base, kY'.isOpenEmbedding.isOpen_range.preimage kY.base.hom.2⟩
  have ha₀O : a₀ ∈ OA := by
    refine ⟨(presentationLimitPreAdicSpacePairComap P' PC₀ hP' hPC₀ hsheafC₀ φ').base c₀₀, ?_⟩
    have h1 := congrArg (fun m ↦ m.base c₀₀) hsq'
    simpa [hc₀₀, ha₀] using h1
  obtain ⟨RA, hRA, ha₀R, hRAO⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens S.plus) ha₀O
  obtain ⟨TA, sA, hTA, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRA
  refine ⟨TA, sA, hTA, ha₀R, ?_⟩
  let LA := Localization.Away sA
  have hdenA := P.hasDenominatorPower_of_isOpen_span TA sA LA hTA
  let _ := P.locUniformSpace TA sA LA hdenA
  have _ := P.isUniformAddGroup_locUniformSpace TA sA LA hdenA
  have _ := P.isTopologicalRing_locUniformSpace TA sA LA hdenA
  have _ := P.isHuberRing_completion_locTopology TA sA LA hdenA
  let S₁ := P.rationalLocalizationPair S hP TA sA LA hdenA
  let P₁ := P.completionLocalization TA sA LA hdenA
  have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP TA sA LA hdenA
  have hsheafA₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S₁.plus))
      (presentationLimitPresheaf P₁ S₁.plus) :=
    isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP TA sA LA hdenA hTA hsheafA
  let ιA := presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
    (P.toCompletionLocHom S hP TA sA LA hdenA)
  have hιA_imm : PreAdicSpace.IsOpenImmersion ιA := by
    rw [show ιA = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P hP TA sA LA hdenA
      hTA hsheafA₁
  have hιA_range : Set.range ιA.base = (spaBasicOpen S.plus TA sA : Set (spa S.plus)) := by
    rw [show ιA = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P hP TA sA LA hdenA
      hsheafA₁
  let kY₁ := ιA ≫ kY
  have hkY₁_imm : PreAdicSpace.IsOpenImmersion kY₁ := PreAdicSpace.IsOpenImmersion.comp ιA kY
  -- Lift `kY₁` across `kY'` to obtain `l₁ : Spa(A₁) ⟶ Spa(A')` and `α₁ : S' → S₁`.
  have hrange₁ : Set.range kY₁.base ⊆ Set.range kY'.base := by
    rintro _ ⟨z, rfl⟩
    have hz : (ιA.base z : spa S.plus) ∈ (spaBasicOpen S.plus TA sA : Set (spa S.plus)) :=
      hιA_range ▸ ⟨z, rfl⟩
    exact hRAO hz
  let l₁ := PreAdicSpace.IsOpenImmersion.lift kY' kY₁ hrange₁
  have hl₁_fac : l₁ ≫ kY' = kY₁ := PreAdicSpace.IsOpenImmersion.lift_fac kY' kY₁ hrange₁
  let α₁ := presentationLimitHomPairHom P' P₁ S' S₁ hP' hP₁ l₁
  -- 3. Shrink `Spa(C₀)` around `c₀₀` to a rational open `R(TC / sC)` whose image in `Y` lies in
  -- `Set.range kY₁.base`.
  let OC : Opens (presentationLimitPreAdicSpace PC₀ U₀.plus
      U₀.isRingOfIntegralElements.isPowerBounded_of_mem hPC₀) :=
    ⟨(kX₀ ≫ f.hom).base ⁻¹' Set.range kY₁.base,
      kY₁.isOpenEmbedding.isOpen_range.preimage (kX₀ ≫ f.hom).base.hom.2⟩
  have hc₀₀O : c₀₀ ∈ OC := by
    have ha₀_mem : (a₀ : spa S.plus) ∈ Set.range ιA.base :=
      hιA_range.symm ▸ (ha₀R : (a₀ : spa S.plus) ∈ (spaBasicOpen S.plus TA sA : Set (spa S.plus)))
    obtain ⟨a₁, ha₁⟩ := ha₀_mem
    refine ⟨a₁, ?_⟩
    simpa [kY₁, hc₀₀, ← ha₀] using congrArg kY.base ha₁
  obtain ⟨RC, hRC, hc₀₀R, hRCO⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens U₀.plus) hc₀₀O
  obtain ⟨TC, sC, hTC, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRC
  let LC := Localization.Away sC
  have hdenC := PC₀.hasDenominatorPower_of_isOpen_span TC sC LC hTC
  let _ := PC₀.locUniformSpace TC sC LC hdenC
  have _ := PC₀.isUniformAddGroup_locUniformSpace TC sC LC hdenC
  have _ := PC₀.isTopologicalRing_locUniformSpace TC sC LC hdenC
  have _ := PC₀.isHuberRing_completion_locTopology TC sC LC hdenC
  let U₁ := PC₀.rationalLocalizationPair U₀ hPC₀ TC sC LC hdenC
  let PC₁ := PC₀.completionLocalization TC sC LC hdenC
  have hPC₁ : PC₁.ringOfDefinition ≤ U₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact PC₀.completionLocalization_ringOfDefinition_le_completedPlusSubring U₀.plus hPC₀ TC sC LC
      hdenC
  have hsheafC₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U₁.plus))
      (presentationLimitPresheaf PC₁ U₁.plus) :=
    isSheaf_presentationLimitPresheaf_rationalLocalizationPair PC₀ U₀ hPC₀ TC sC LC hdenC hTC
      hsheafC₀
  let ιC := presentationLimitPreAdicSpacePairComap PC₀ PC₁ hPC₀ hPC₁ hsheafC₁
    (PC₀.toCompletionLocHom U₀ hPC₀ TC sC LC hdenC)
  have hιC_imm : PreAdicSpace.IsOpenImmersion ιC := by
    rw [show ιC = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom PC₀ hPC₀ TC sC LC
      hdenC hTC hsheafC₁
  have hιC_range : Set.range ιC.base = (spaBasicOpen U₀.plus TC sC : Set (spa U₀.plus)) := by
    rw [show ιC = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base PC₀ hPC₀ TC sC LC hdenC
      hsheafC₁
  let kX₁ := ιC ≫ kX₀
  have hkX₁_imm : PreAdicSpace.IsOpenImmersion kX₁ := PreAdicSpace.IsOpenImmersion.comp ιC kX₀
  have hc₀₀_mem : (c₀₀ : spa U₀.plus) ∈ Set.range ιC.base :=
    hιC_range.symm ▸
      (hc₀₀R : (c₀₀ : spa U₀.plus) ∈ (spaBasicOpen U₀.plus TC sC : Set (spa U₀.plus)))
  obtain ⟨c₁, hc₁⟩ := hc₀₀_mem
  -- 4. Lift `kX₁ ≫ f.hom` across `kY₁` and cancel `α₁` on the right via `Cancel.lean`.
  have hrangeC : Set.range (kX₁ ≫ f.hom).base ⊆ Set.range kY₁.base := by
    rintro _ ⟨z, rfl⟩
    have hz : (ιC.base z : spa U₀.plus) ∈ (spaBasicOpen U₀.plus TC sC : Set (spa U₀.plus)) :=
      hιC_range ▸ ⟨z, rfl⟩
    exact hRCO hz
  let q := PreAdicSpace.IsOpenImmersion.lift kY₁ (kX₁ ≫ f.hom) hrangeC
  have hq_fac : q ≫ kY₁ = kX₁ ≫ f.hom :=
    PreAdicSpace.IsOpenImmersion.lift_fac kY₁ (kX₁ ≫ f.hom) hrangeC
  let β := presentationLimitHomPairHom P₁ PC₁ S₁ U₁ hP₁ hPC₁ q
  have hql₁ : q ≫ l₁ = ιC ≫ presentationLimitPreAdicSpacePairComap P' PC₀ hP' hPC₀ hsheafC₀ φ' := by
    rw [← cancel_mono kY', Category.assoc, hl₁_fac, hq_fac, Category.assoc, ← hsq', Category.assoc]
  have hβα : β.comp α₁ = (PC₀.toCompletionLocHom U₀ hPC₀ TC sC LC hdenC).comp φ' := by
    have h := congrArg (presentationLimitHomPairHom P' PC₁ S' U₁ hP' hPC₁) hql₁
    rwa [presentationLimitHomPairHom_comp P' P₁ PC₁ S' S₁ U₁ hP' hP₁ hPC₁,
      ← presentationLimitPreAdicSpacePairComap_comp P' PC₀ PC₁ hP' hPC₀ hPC₁ hsheafC₀ hsheafC₁,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P' PC₁ S' U₁ hP' hPC₁
        hsheafC₁] at h
  have hχ_tft :
      ((PC₀.toCompletionLocHom U₀ hPC₀ TC sC LC hdenC).comp φ').IsTopologicallyFiniteType :=
    PC₀.isTopologicallyFiniteType_toCompletionLocHom_comp U₀ hPC₀ TC sC LC hdenC φ' hφ'
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTC)
  have hβ_tft : β.IsTopologicallyFiniteType :=
    Pair.Hom.IsTopologicallyFiniteType.of_comp (hβα ▸ hχ_tft)
  refine ⟨UniformSpace.Completion LC, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, U₁, PC₁, hPC₁, hsheafC₁, kX₁, hkX₁_imm,
    β, hβ_tft, c₁, ?_, ?_⟩
  · simpa [kX₁, ← hc₀₀] using congrArg kX₀.base hc₁
  · rw [presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom P₁ PC₁ S₁ U₁ hP₁ hPC₁
      hsheafC₁]
    exact hq_fac

/-- **Composition of morphisms locally of finite type** (Wedhorn, Proposition 8.50(1)): if
`f : X ⟶ Y` and `g : Y ⟶ Z` are locally of finite type, then `f ≫ g` is locally of finite type. No
Tate hypothesis is needed on any of the spaces. -/
theorem LocallyOfFiniteType.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyOfFiniteType f) (hg : LocallyOfFiniteType g) :
    LocallyOfFiniteType (f ≫ g) := by
  refine (locallyOfFiniteType_iff_chartLocally (f ≫ g)).mpr <| (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, -, B, _, _, _, _, _, _, _, T, P', hP', hsheafB,
    kY, hkY, kZ, hkZ, ψ, hψ, b₀, hb₀, hsq_g⟩ :=
    hg.exists_complete_openImmersion_chart (f.hom.base x)
  obtain ⟨TB, sB, hTB, -, C, _, _, _, _, _, _, _, U, PC, hPC, hsheafC, kX, hkX, β, hβ, c₀, hc₀,
    hsq_f⟩ := hf.exists_openImmersion_over_rationalLocalization P' hP' hsheafB kY x hb₀
  let LB := Localization.Away sB
  have hdenB := P'.hasDenominatorPower_of_isOpen_span TB sB LB hTB
  let _ := P'.locUniformSpace TB sB LB hdenB
  have _ := P'.isUniformAddGroup_locUniformSpace TB sB LB hdenB
  have _ := P'.isTopologicalRing_locUniformSpace TB sB LB hdenB
  have _ := P'.isHuberRing_completion_locTopology TB sB LB hdenB
  let T₁ := P'.rationalLocalizationPair T hP' TB sB LB hdenB
  let P₁' := P'.completionLocalization TB sB LB hdenB
  have hP₁' : P₁'.ringOfDefinition ≤ T₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring T.plus hP' TB sB LB
      hdenB
  have hsheafB₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T₁.plus))
      (presentationLimitPresheaf P₁' T₁.plus) :=
    isSheaf_presentationLimitPresheaf_rationalLocalizationPair P' T hP' TB sB LB hdenB hTB hsheafB
  let ψ₁ := (P'.toCompletionLocHom T hP' TB sB LB hdenB).comp ψ
  have hψ₁ : ψ₁.IsTopologicallyFiniteType :=
    P'.isTopologicallyFiniteType_toCompletionLocHom_comp T hP' TB sB LB hdenB ψ hψ
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTB)
  let χ := β.comp ψ₁
  have hχ : χ.IsTopologicallyFiniteType := hβ.comp hψ₁
  refine exists_chart_of_openImmersion_sq hP hPC hsheafC kX kZ χ hχ hc₀ ?_
  rw [presentationLimitPreAdicSpacePairComap_comp P P₁' PC hP hP₁' hPC hsheafB₁ hsheafC,
    presentationLimitPreAdicSpacePairComap_comp P P' P₁' hP hP' hP₁' hsheafB hsheafB₁]
  simp only [Category.assoc]
  rw [hsq_g, reassoc_of% hsq_f, ObjectProperty.FullSubcategory.comp_hom]

/-- `LocallyOfFiniteType` is stable under composition in `AdicSpace`. -/
instance LocallyOfFiniteType.isStableUnderComposition :
    LocallyOfFiniteType.{u}.IsStableUnderComposition where
  comp_mem _ _ hf hg := hf.comp hg

/-- `LocallyOfFiniteType` is a multiplicative morphism property on `AdicSpace`. -/
instance LocallyOfFiniteType.isMultiplicative :
    LocallyOfFiniteType.{u}.IsMultiplicative where

/-- **Right-cancellation of morphisms locally of finite type** (Wedhorn, Proposition 8.50(2)): if
`f : X ⟶ Y` and `g : Y ⟶ Z` are morphisms of adic spaces such that `f ≫ g` is locally of finite
type, then `f` is locally of finite type, with no finiteness or separatedness assumption on `g`. -/
theorem LocallyOfFiniteType.of_comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hfg : LocallyOfFiniteType (f ≫ g)) : LocallyOfFiniteType f := by
  classical
  refine (locallyOfFiniteType_iff_chartLocally f).mpr <| (chartLocally_iff _).mpr fun x ↦ ?_
  -- 1. Choose a complete FT chart `(kX : Spa(C) ⟶ X, kZ : Spa(A) ⟶ Z, χ : A → C)` for `f ≫ g`.
  obtain ⟨A, _, _, _, _, _, _, _, S, P, hP, -, C, _, _, _, _, _, _, _, U, PC, hPC, hsheafC,
    kX, hkX, kZ, hkZ, χ, hχ, c₀, hc₀, hsq_fg⟩ := hfg.exists_complete_openImmersion_chart x
  -- 2. Choose an open affinoid `W ⊆ g⁻¹(Set.range kZ)` of `Y` containing `f(x)` and complete it.
  let OY : Opens Y.obj :=
    ⟨g.hom.base ⁻¹' Set.range kZ.base, kZ.isOpenEmbedding.isOpen_range.preimage g.hom.base.hom.2⟩
  have hfxO : f.hom.base x ∈ OY := by
    refine ⟨(presentationLimitPreAdicSpacePairComap P PC hP hPC hsheafC χ).base c₀, ?_⟩
    have h1 := congrArg (fun m ↦ m.base c₀) hsq_fg
    simpa [hc₀] using h1
  obtain ⟨W, hW, hfxW, hWO⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_affinoidOpens Y.property.isLocallyAffinoid) hfxO
  obtain ⟨B, _, _, _, _, _, _, _, T, P', hP', -, ⟨eW⟩⟩ :=
    Y.property.isSheafy.exists_complete_isSheaf_of_mem_affinoidOpens hW
  let kY := eW.inv ≫ Y.obj.ofRestrict W.isOpenEmbedding
  have hkY : PreAdicSpace.IsOpenImmersion kY := PreAdicSpace.IsOpenImmersion.comp _ _
  let b₀ := eW.hom.base ⟨f.hom.base x, hfxW⟩
  have hb₀ : kY.base b₀ = f.hom.base x := by
    have hb : (eW.hom ≫ eW.inv).base ⟨f.hom.base x, hfxW⟩ = ⟨f.hom.base x, hfxW⟩ := by
      simp
      rfl
    exact congrArg (Y.obj.ofRestrict W.isOpenEmbedding).base hb
  have hrangeY : Set.range (kY ≫ g.hom).base ⊆ Set.range kZ.base := by
    rintro _ ⟨b, rfl⟩
    exact hWO (eW.inv.base b).2
  let p := PreAdicSpace.IsOpenImmersion.lift kZ (kY ≫ g.hom) hrangeY
  have hp_fac : p ≫ kZ = kY ≫ g.hom :=
    PreAdicSpace.IsOpenImmersion.lift_fac kZ (kY ≫ g.hom) hrangeY
  let ψ := presentationLimitHomPairHom P P' S T hP hP' p
  -- 3. Shrink `Spa(C)` around `c₀` to a rational open `R(TC / sC)` mapping into `Set.range kY`.
  let OC : Opens (presentationLimitPreAdicSpace PC U.plus
      U.isRingOfIntegralElements.isPowerBounded_of_mem hPC) :=
    ⟨(kX ≫ f.hom).base ⁻¹' Set.range kY.base,
      kY.isOpenEmbedding.isOpen_range.preimage (kX ≫ f.hom).base.hom.2⟩
  have hc₀O : c₀ ∈ OC := ⟨b₀, by simpa [hc₀] using hb₀⟩
  obtain ⟨RC, hRC, hc₀R, hRCO⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens U.plus) hc₀O
  obtain ⟨TC, sC, hTC, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRC
  let LC := Localization.Away sC
  have hdenC := PC.hasDenominatorPower_of_isOpen_span TC sC LC hTC
  let _ := PC.locUniformSpace TC sC LC hdenC
  have _ := PC.isUniformAddGroup_locUniformSpace TC sC LC hdenC
  have _ := PC.isTopologicalRing_locUniformSpace TC sC LC hdenC
  have _ := PC.isHuberRing_completion_locTopology TC sC LC hdenC
  let U₁ := PC.rationalLocalizationPair U hPC TC sC LC hdenC
  let PC₁ := PC.completionLocalization TC sC LC hdenC
  have hPC₁ : PC₁.ringOfDefinition ≤ U₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact PC.completionLocalization_ringOfDefinition_le_completedPlusSubring U.plus hPC TC sC LC
      hdenC
  have hsheafC₁ : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U₁.plus))
      (presentationLimitPresheaf PC₁ U₁.plus) :=
    isSheaf_presentationLimitPresheaf_rationalLocalizationPair PC U hPC TC sC LC hdenC hTC hsheafC
  let ιC := presentationLimitPreAdicSpacePairComap PC PC₁ hPC hPC₁ hsheafC₁
    (PC.toCompletionLocHom U hPC TC sC LC hdenC)
  have hιC_imm : PreAdicSpace.IsOpenImmersion ιC := by
    rw [show ιC = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom PC hPC TC sC LC
      hdenC hTC hsheafC₁
  have hιC_range : Set.range ιC.base = (spaBasicOpen U.plus TC sC : Set (spa U.plus)) := by
    rw [show ιC = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base PC hPC TC sC LC hdenC
      hsheafC₁
  let kX₁ := ιC ≫ kX
  have hkX₁_imm : PreAdicSpace.IsOpenImmersion kX₁ := PreAdicSpace.IsOpenImmersion.comp ιC kX
  have hc₀_mem : (c₀ : spa U.plus) ∈ Set.range ιC.base :=
    hιC_range.symm ▸ (hc₀R : (c₀ : spa U.plus) ∈ (spaBasicOpen U.plus TC sC : Set (spa U.plus)))
  obtain ⟨c₁, hc₁⟩ := hc₀_mem
  -- 4. Lift `kX₁ ≫ f.hom` across `kY` and cancel `ψ` on the right via `Cancel.lean`.
  have hrangeC : Set.range (kX₁ ≫ f.hom).base ⊆ Set.range kY.base := by
    rintro _ ⟨z, rfl⟩
    have hz : (ιC.base z : spa U.plus) ∈ (spaBasicOpen U.plus TC sC : Set (spa U.plus)) :=
      hιC_range ▸ ⟨z, rfl⟩
    exact hRCO hz
  let q := PreAdicSpace.IsOpenImmersion.lift kY (kX₁ ≫ f.hom) hrangeC
  have hq_fac : q ≫ kY = kX₁ ≫ f.hom :=
    PreAdicSpace.IsOpenImmersion.lift_fac kY (kX₁ ≫ f.hom) hrangeC
  let φ := presentationLimitHomPairHom P' PC₁ T U₁ hP' hPC₁ q
  have hqp : q ≫ p = ιC ≫ presentationLimitPreAdicSpacePairComap P PC hP hPC hsheafC χ := by
    rw [← cancel_mono kZ, Category.assoc, hp_fac, ← Category.assoc q, hq_fac]
    dsimp only [kX₁]
    rw [Category.assoc, Category.assoc,
      ← ObjectProperty.FullSubcategory.comp_hom (f := f) (g := g), ← hsq_fg, Category.assoc]
  have hφψ : φ.comp ψ = (PC.toCompletionLocHom U hPC TC sC LC hdenC).comp χ := by
    have h := congrArg (presentationLimitHomPairHom P PC₁ S U₁ hP hPC₁) hqp
    rwa [presentationLimitHomPairHom_comp P P' PC₁ S T U₁ hP hP' hPC₁,
      ← presentationLimitPreAdicSpacePairComap_comp P PC PC₁ hP hPC hPC₁ hsheafC hsheafC₁,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P PC₁ S U₁ hP hPC₁
        hsheafC₁] at h
  have hχ₁ : ((PC.toCompletionLocHom U hPC TC sC LC hdenC).comp χ).IsTopologicallyFiniteType :=
    PC.isTopologicallyFiniteType_toCompletionLocHom_comp U hPC TC sC LC hdenC χ hχ
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTC)
  have hφ : φ.IsTopologicallyFiniteType :=
    Pair.Hom.IsTopologicallyFiniteType.of_comp (hφψ ▸ hχ₁)
  refine exists_chart_of_openImmersion_sq (b₀ := c₁) hP' hPC₁ hsheafC₁ kX₁ kY φ hφ ?_ ?_
  · simpa [kX₁, ← hc₀] using congrArg kX.base hc₁
  · rw [presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom P' PC₁ T U₁ hP' hPC₁
      hsheafC₁]
    exact hq_fac

/-- **Restriction of morphisms locally of finite type along open immersions of the source**
(Wedhorn, Proposition 8.50): if `g ≫ iV = iU ≫ f` for an open immersion `iU : U ⟶ X` and any
morphism `iV : V ⟶ Y` (in particular an open immersion) and `f` is locally of finite type, then `g`
is locally of finite type. -/
theorem LocallyOfFiniteType.restrict {U V : AdicSpace.{u}} {iU : U ⟶ X} {iV : V ⟶ Y}
    {f : X ⟶ Y} {g : U ⟶ V} [PreAdicSpace.IsOpenImmersion iU.hom]
    (hcomm : g ≫ iV = iU ≫ f) (hf : LocallyOfFiniteType f) : LocallyOfFiniteType g :=
  LocallyOfFiniteType.of_comp (g := iV)
    (hcomm ▸ (LocallyOfFiniteType.of_isOpenImmersion iU).comp hf)

end OpenImmersionCharts

/-! ### Affinoid and discrete affinoid morphisms -/

section Affinoid

/-- **Affinoid morphisms**: for a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` topologically of
finite type with `B` complete and Hausdorff, between pairs whose adic spectra are adic spaces, the
induced morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` in `AdicSpace` is locally of finite type. -/
theorem locallyOfFiniteType_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
    [IsHuberRing B] {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP))
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFiniteType (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) :=
  ValuationSpectrum.locallyOfFiniteType_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf φ hφ

/-- For complete Hausdorff `B`, `comapOfPresentation` is locally of finite type whenever the
underlying morphism of Huber pairs is topologically of finite type. -/
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
  rw [comapOfPresentation_eq_homMk_presentationLimitPreAdicSpaceComap]
  exact locallyOfFiniteType_presentationLimitPreAdicSpaceComap P P' hS hT hsheafT
    (ofPresentation S P hS hsheafS).property φ hφ

/-- Comparing `LocallyOfFiniteType` on `comapOfPair` with `comapOfPresentation` for any compatible
pairs of definition. -/
theorem locallyOfFiniteType_comapOfPair_iff_comapOfPresentation {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
    (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus) (φ : Pair.Hom S T) :
    LocallyOfFiniteType (comapOfPair hS hT φ) ↔
      LocallyOfFiniteType
        (comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP') φ) := by
  rw [← MorphismProperty.cancel_right_of_respectsIso (@LocallyOfFiniteType.{u}) _
      (ofPairIsoOfPresentation S hS P hP).hom,
    ← ofPairIsoOfPresentation_hom_comapOfPresentation hS hT P hP P' hP' φ,
    MorphismProperty.cancel_left_of_respectsIso (@LocallyOfFiniteType.{u})]

/-- For complete Hausdorff `B`, `comapOfPair` is locally of finite type whenever the underlying
morphism of Huber pairs is topologically of finite type. -/
theorem locallyOfFiniteType_comapOfPair {A : Type u} [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B] [UniformSpace B]
    [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B] [IsHuberRing B]
    {S : Pair A} {T : Pair B}
    (hS : IsSheafyForEveryPresentation S.plus) (hT : IsSheafyForEveryPresentation T.plus)
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType) :
    LocallyOfFiniteType (comapOfPair hS hT φ) := by
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  exact (locallyOfFiniteType_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mpr
    (locallyOfFiniteType_comapOfPresentation S P hP (hS.isSheaf P hP) T P' hP' (hT.isSheaf P' hP')
      φ hφ)

/-- **Discrete affinoid morphisms locally of finite type have finite-type ring homomorphisms**: if
`A` and `B` carry the discrete topology and `comapOfPair hS hT φ : Spa(B, B⁺) ⟶ Spa(A, A⁺)` is
locally of finite type, then `φ.toRingHom : A →+* B` is algebraically of finite type. -/
theorem LocallyOfFiniteType.finiteType_of_discreteTopology {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] {B : Type u} [CommRing B]
    [TopologicalSpace B] [IsTopologicalRing B] [DiscreteTopology B] {S : Pair A} {T : Pair B}
    {hS : IsSheafyForEveryPresentation S.plus} {hT : IsSheafyForEveryPresentation T.plus}
    {φ : Pair.Hom S T} (hf : LocallyOfFiniteType (comapOfPair hS hT φ)) :
    φ.toRingHom.FiniteType := by
  classical
  let _ : UniformSpace A := IsTopologicalAddGroup.rightUniformSpace A
  have : IsUniformAddGroup A := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity A := IsRightUniformAddGroup.discreteUniformity
  let _ : UniformSpace B := IsTopologicalAddGroup.rightUniformSpace B
  have : IsUniformAddGroup B := isUniformAddGroup_of_addCommGroup
  have : DiscreteUniformity B := IsRightUniformAddGroup.discreteUniformity
  obtain ⟨P, hP, _⟩ := hS.exists_compatible_isSheaf
  obtain ⟨P', hP', _⟩ := hT.exists_compatible_isSheaf
  have hsheafA := hS.isSheaf P hP
  have hsheafB := hT.isSheaf P' hP'
  let q := comapOfPresentation S P hP hsheafA T P' hP' hsheafB φ
  have hq : LocallyOfFiniteType q :=
    (locallyOfFiniteType_comapOfPair_iff_comapOfPresentation hS hT P hP P' hP' φ).mp hf
  -- For each `y : spa T.plus`, find a rational open `R(TB y / sB y)` around `y` whose coordinate
  -- ring `B_{sB y}` is finite type over `A`.
  have hloc : ∀ y : spa T.plus, ∃ (TB : Finset B) (sB : B),
      y.1 ∈ rationalSubset T.plus TB sB ∧
      ((algebraMap B (Localization.Away sB)).comp φ.toRingHom).FiniteType := by
    intro y
    let y₀ : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP' := y
    let kA : presentationLimitPreAdicSpace P S.plus
        S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶
        (ofPresentation S P hP hsheafA).obj := 𝟙 _
    obtain ⟨TA, sA, hTA, -, C, _, _, _, _, _, _, _, U, PC, hPC, hsheafC, kX, hkX, β, hβ, c₀,
      hc₀, hsq⟩ := hq.exists_openImmersion_over_rationalLocalization P hP hsheafA kA y₀ rfl
    -- Shrink `Spa(B, B⁺)` around `y₀` into `Set.range kX.base`.
    let OB : Opens (presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP') :=
      ⟨Set.range kX.base, kX.isOpenEmbedding.isOpen_range⟩
    have hyO : y₀ ∈ OB := ⟨c₀, hc₀⟩
    obtain ⟨RB, hRB, hyR, hRBO⟩ :=
      Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens T.plus) hyO
    obtain ⟨TB, sB, hTB, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRB
    refine ⟨TB, sB, mem_spaBasicOpen.mp hyR, ?_⟩
    let LA := Localization.Away sA
    have hdenA := P.hasDenominatorPower_of_isOpen_span TA sA LA hTA
    let _ := P.locUniformSpace TA sA LA hdenA
    have _ := P.isUniformAddGroup_locUniformSpace TA sA LA hdenA
    have _ := P.isTopologicalRing_locUniformSpace TA sA LA hdenA
    have _ := P.isHuberRing_completion_locTopology TA sA LA hdenA
    let S₁ := P.rationalLocalizationPair S hP TA sA LA hdenA
    let P₁ := P.completionLocalization TA sA LA hdenA
    have hP₁ : P₁.ringOfDefinition ≤ S₁.plus := by
      rw [rationalLocalizationPair_plus]
      exact P.completionLocalization_ringOfDefinition_le_completedPlusSubring S.plus hP TA sA LA
        hdenA
    have hsheafA₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP TA sA LA
      hdenA hTA hsheafA
    let LB := Localization.Away sB
    have hdenB := P'.hasDenominatorPower_of_isOpen_span TB sB LB hTB
    let _ := P'.locUniformSpace TB sB LB hdenB
    have _ := P'.isUniformAddGroup_locUniformSpace TB sB LB hdenB
    have _ := P'.isTopologicalRing_locUniformSpace TB sB LB hdenB
    have _ := P'.isHuberRing_completion_locTopology TB sB LB hdenB
    let T₁ := P'.rationalLocalizationPair T hP' TB sB LB hdenB
    let P₁' := P'.completionLocalization TB sB LB hdenB
    have hP₁' : P₁'.ringOfDefinition ≤ T₁.plus := by
      rw [rationalLocalizationPair_plus]
      exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring T.plus hP' TB sB LB
        hdenB
    have hsheafB₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P' T hP' TB sB LB
      hdenB hTB hsheafB
    let ιB := presentationLimitPreAdicSpacePairComap P' P₁' hP' hP₁' hsheafB₁
      (P'.toCompletionLocHom T hP' TB sB LB hdenB)
    have hιB_range : Set.range ιB.base = (spaBasicOpen T.plus TB sB : Set (spa T.plus)) := by
      rw [show ιB = _ from presentationLimitPreAdicSpacePairComap_def ..]
      exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P' hP' TB sB LB hdenB
        hsheafB₁
    have hrangeB : Set.range ιB.base ⊆ Set.range kX.base := by
      rintro _ ⟨z, rfl⟩
      have hz : (ιB.base z : spa T.plus) ∈ (spaBasicOpen T.plus TB sB : Set (spa T.plus)) :=
        hιB_range ▸ ⟨z, rfl⟩
      exact hRBO hz
    let r := PreAdicSpace.IsOpenImmersion.lift kX ιB hrangeB
    have hr_fac : r ≫ kX = ιB := PreAdicSpace.IsOpenImmersion.lift_fac kX ιB hrangeB
    let δ := presentationLimitHomPairHom P' PC T U hP' hPC kX
    let γ := presentationLimitHomPairHom PC P₁' U T₁ hPC hP₁' r
    have hγδ : γ.comp δ = P'.toCompletionLocHom T hP' TB sB LB hdenB := by
      have h := congrArg (presentationLimitHomPairHom P' P₁' T T₁ hP' hP₁') hr_fac
      rwa [presentationLimitHomPairHom_comp P' PC P₁' T U T₁ hP' hPC hP₁',
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P' P₁' T T₁ hP' hP₁'
          hsheafB₁] at h
    have hγ_tft : γ.IsTopologicallyFiniteType :=
      Pair.Hom.IsTopologicallyFiniteType.of_comp (hγδ ▸
        P'.isTopologicallyFiniteType_toCompletionLocHom T hP' TB sB LB hdenB
          (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTB))
    -- Compare the two paths `A → A₁ → C → B₁` and `A → B → B₁` on global sections.
    have hpath : γ.comp (β.comp (P.toCompletionLocHom S hP TA sA LA hdenA)) =
        (P'.toCompletionLocHom T hP' TB sB LB hdenB).comp φ := by
      have hsq' : r ≫ presentationLimitPreAdicSpacePairComap P₁ PC hP₁ hPC hsheafC β ≫
          presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
            (P.toCompletionLocHom S hP TA sA LA hdenA) =
          ιB ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
        have hsq₁ : presentationLimitPreAdicSpacePairComap P₁ PC hP₁ hPC hsheafC β ≫
            presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
              (P.toCompletionLocHom S hP TA sA LA hdenA) =
            kX ≫ presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ := by
          simpa [kA, q] using hsq
        rw [hsq₁, ← Category.assoc, hr_fac]
      have h := congrArg (presentationLimitHomPairHom P P₁' S T₁ hP hP₁') hsq'
      dsimp only [γ]
      rwa [← presentationLimitPreAdicSpacePairComap_comp P P₁ PC hP hP₁ hPC hsheafA₁ hsheafC,
        presentationLimitHomPairHom_comp P PC P₁' S U T₁ hP hPC hP₁',
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P PC S U hP hPC hsheafC,
        ← presentationLimitPreAdicSpacePairComap_comp P P' P₁' hP hP' hP₁' hsheafB hsheafB₁,
        presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P P₁' S T₁ hP hP₁'
          hsheafB₁] at h
    have hcomp_tft :
        ((P'.toCompletionLocHom T hP' TB sB LB hdenB).comp φ).IsTopologicallyFiniteType := by
      rw [← hpath]
      exact hγ_tft.comp (hβ.comp (P.isTopologicallyFiniteType_toCompletionLocHom S hP TA sA LA
        hdenA (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTA)))
    have hcomp_ft : ((P'.toCompletionLocHom T hP' TB sB LB hdenB).toRingHom.comp
        φ.toRingHom).FiniteType := by
      rw [← Pair.Hom.toRingHom_comp]
      exact hcomp_tft.isTopologicallyFiniteType_toRingHom.finiteType
    let eB := P'.completionLocEquivOfDiscreteTopology (TB : Set B) sB LB hdenB
    have heq : (algebraMap B LB).comp φ.toRingHom =
        eB.symm.toRingHom.comp
          ((P'.toCompletionLocHom T hP' TB sB LB hdenB).toRingHom.comp φ.toRingHom) := by
      ext a
      simp [eB, toRingHom_toCompletionLocHom, toCompletionLoc_apply]
    rw [heq]
    exact (RingHom.FiniteType.of_surjective eB.symm.toRingHom eB.symm.surjective).comp hcomp_ft
  choose TB sB hyR hft using hloc
  have : IsLocalization.Away (1 : B) B :=
    IsLocalization.self (by rintro _ ⟨n, rfl⟩; simp)
  have hcov : rationalSubset T.plus ({1} : Finset B) 1 ⊆
      ⋃ y : spa T.plus, rationalSubset T.plus (TB y) (sB y) := by
    intro v hv
    rw [rationalSubset_singleton_one] at hv
    exact Set.mem_iUnion.mpr ⟨⟨v, hv⟩, hyR ⟨v, hv⟩⟩
  have hspan : Ideal.span (Set.range sB) = ⊤ := by
    simpa using span_eq_top_of_rationalSubset_subset_iUnion (Aplus := T.plus) (T := {1}) (s := 1) B
      (fun _ _ ↦ isOpen_discrete _) hcov
  refine RingHom.finiteType_ofLocalizationSpanTarget φ.toRingHom (Set.range sB) hspan ?_
  rintro ⟨_, y, rfl⟩
  exact hft y

/-- **Discrete affinoid comparison for `LocallyOfFiniteType`**: for discrete commutative rings `A`
and `B` with trivial plus rings `Pair.discrete A = (A, A)` and `Pair.discrete B = (B, B)`, the
induced morphism `Spa(B, B) ⟶ Spa(A, A)` is locally of finite type if and only if `φ.toRingHom` is
algebraically of finite type (`RingHom.FiniteType`). -/
theorem locallyOfFiniteType_comapOfPair_discrete_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] {B : Type u} [CommRing B]
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
