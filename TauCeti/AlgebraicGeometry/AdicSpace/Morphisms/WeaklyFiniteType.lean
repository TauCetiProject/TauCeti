/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.Adic
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyHuberStandard
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyOfFiniteType.OpenImmersion
public import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Adic

import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.Affinoid.Comap
import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.BaseChange
import TauCeti.RingTheory.Huber.LocalizationTopology.FiniteType
import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Morphisms of adic spaces locally of weakly finite type

A morphism `f : X ⟶ Y` of adic spaces is *locally of weakly finite type* (Wedhorn, Definition
8.48(1); Huber 1994, §3) if every point of `X` has an open neighbourhood `U`, mapped by `f` into
an open `V` of `Y`, such that `U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for Huber pairs, `B` complete
and Hausdorff, under which `f` restricted to `U → V` is the morphism induced by a morphism of
Huber pairs `(A, A⁺) → (B, B⁺)` whose ring homomorphism `A → B` is topologically of finite type
(`TauCeti.Huber.IsTopologicallyFiniteType`). No condition is put on the plus rings: this is what
distinguishes it from `TauCeti.PreAdicSpace.LocallyOfFiniteType`, which asks the morphism of
pairs itself to be topologically of finite type (Wedhorn, Definition 8.42).

The class sits in Huber's hierarchy of finiteness conditions (Huber 1996, §1.2): a morphism
locally of finite type is locally of weakly finite type, and a morphism locally of weakly finite
type is adic, because a homomorphism topologically of finite type is adic. Identities, open
immersions and isomorphisms are locally of weakly finite type, as is the morphism of affinoid adic
spaces induced by a morphism of Huber pairs whose ring homomorphism is topologically of finite
type. Being locally of weakly finite type is not a global condition on affinoids: the ring
homomorphism of an affinoid morphism locally of weakly finite type need not be topologically of
finite type (Wedhorn, Remark 8.52), so the last statement has no converse.

Because noetherian type and Huber's standing class ascend along ring homomorphisms topologically of
finite type (`TauCeti.Huber.IsNoetherianType.of_isTopologicallyFiniteType`,
`TauCeti.Huber.IsHuberStandard.of_isTopologicallyFiniteType`), and topological finite type cancels
on the right along continuous ring homomorphisms
(`TauCeti.Huber.IsTopologicallyFiniteType.of_comp`), both `TauCeti.AdicSpace.IsLocallyNoetherian`
and `TauCeti.AdicSpace.IsLocallyHuberStandard` ascend from the target of a morphism locally of
weakly finite type (and hence of a morphism locally of finite type) to its source.

## Main definitions

* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType`: morphisms of adic spaces locally of weakly finite
  type.

## Main results

* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.isAdic`: a morphism locally of weakly finite type
  is adic.
* `TauCeti.PreAdicSpace.LocallyOfFiniteType.locallyOfWeaklyFiniteType`: a morphism of adic spaces
  locally of finite type is locally of weakly finite type.
* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.of_isOpenImmersion`: open immersions are locally of
  weakly finite type.
* `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.containsIdentities`,
  `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType.respectsIso`: identities are locally of weakly finite
  type, and the property is invariant under isomorphisms of the source and of the target; so
  isomorphisms are locally of weakly finite type (`CategoryTheory.MorphismProperty.of_isIso`).
* `TauCeti.AdicSpace.locallyOfWeaklyFiniteType_presentationLimitPreAdicSpaceComap`: the morphism
  `Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by a morphism of Huber pairs whose ring homomorphism is
  topologically of finite type is locally of weakly finite type.
* `TauCeti.AdicSpace.IsLocallyNoetherian.of_locallyOfWeaklyFiniteType` and
  `TauCeti.AdicSpace.IsLocallyNoetherian.of_locallyOfFiniteType`: locally noetherian structure
  ascends along morphisms locally of weakly finite type and locally of finite type.
* `TauCeti.AdicSpace.IsLocallyHuberStandard.of_locallyOfWeaklyFiniteType` and
  `TauCeti.AdicSpace.IsLocallyHuberStandard.of_locallyOfFiniteType`: being locally of Huber's
  standing class ascends along morphisms locally of weakly finite type and locally of finite type.

## References

* T. Wedhorn, *Adic Spaces*, arXiv:1910.05934v1, Definitions 8.42 and 8.48, Remark 8.52.
* R. Huber, *A generalization of formal schemes and rigid analytic varieties*, Math. Z. 217
  (1994), §3.
* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), (1.1.1) and §1.2.
-/

public section

open CategoryTheory TopologicalSpace

namespace TauCeti

open Huber

universe u

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

/-- **Morphisms locally of weakly finite type** (Wedhorn, Definition 8.48(1)): a morphism
`f : X ⟶ Y` of adic spaces is *locally of weakly finite type* when every point `x` of `X` has an
open neighbourhood `U`, mapped by `f` into an open `V` of `Y`, together with Huber pairs `(A, A⁺)`
and `(B, B⁺)`, `B` complete and Hausdorff with `Spa(B, B⁺)` having a sheaf as structure presheaf,
a morphism `φ : (A, A⁺) → (B, B⁺)` whose ring homomorphism is topologically of finite type, and
isomorphisms identifying `X` restricted to `U` with `Spa(B, B⁺)` and `Y` restricted to `V` with
`Spa(A, A⁺)`, under which `f` becomes the morphism induced by `φ`; that is, `f` is chart-locally
topologically of finite type on rings (`TauCeti.PreAdicSpace.chartLocally`). -/
def LocallyOfWeaklyFiniteType : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  chartLocally (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom) f.hom

variable {X Y : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.LocallyOfWeaklyFiniteType`. -/
theorem locallyOfWeaklyFiniteType_iff_chartLocally (f : X ⟶ Y) :
    LocallyOfWeaklyFiniteType f ↔
      chartLocally (fun φ ↦ IsTopologicallyFiniteType φ.toRingHom) f.hom :=
  Iff.rfl

/-- **A morphism locally of weakly finite type is adic** (Huber 1996, §1.2): on each chart it is
induced by a homomorphism topologically of finite type, which is adic. -/
theorem LocallyOfWeaklyFiniteType.isAdic {f : X ⟶ Y} (hf : LocallyOfWeaklyFiniteType f) :
    IsAdic f :=
  (isAdic_iff_chartLocally f).mpr <| chartLocally_mono (fun _ hφ ↦ hφ.isAdicHom)
    ((locallyOfWeaklyFiniteType_iff_chartLocally f).mp hf)

end AdicSpace

/-- **A morphism of adic spaces locally of finite type is locally of weakly finite type**: the ring
homomorphism of a morphism of Huber pairs topologically of finite type is topologically of finite
type. -/
theorem PreAdicSpace.LocallyOfFiniteType.locallyOfWeaklyFiniteType {X Y : AdicSpace.{u}}
    {f : X ⟶ Y} (hf : PreAdicSpace.LocallyOfFiniteType f.hom) :
    AdicSpace.LocallyOfWeaklyFiniteType f :=
  (AdicSpace.locallyOfWeaklyFiniteType_iff_chartLocally f).mpr <|
    PreAdicSpace.chartLocally_mono (fun _ hφ ↦ hφ.isTopologicallyFiniteType_toRingHom)
      ((locallyOfFiniteType_iff f.hom).mp hf)

namespace AdicSpace

open PreAdicSpace ValuationSpectrum

variable {X Y : AdicSpace.{u}}

/-- **Open immersions are locally of weakly finite type**: they are locally of finite type. -/
theorem LocallyOfWeaklyFiniteType.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] : LocallyOfWeaklyFiniteType f :=
  (locallyOfFiniteType_of_isOpenImmersion f.hom X.property).locallyOfWeaklyFiniteType

/-- **Identities are locally of weakly finite type.** -/
instance LocallyOfWeaklyFiniteType.containsIdentities :
    LocallyOfWeaklyFiniteType.{u}.ContainsIdentities where
  id_mem X := (locallyOfFiniteType_id X.property).locallyOfWeaklyFiniteType

/-- **Being locally of weakly finite type is invariant under isomorphisms** of the source and of
the target: it is the inverse image of a chart-local property along the inclusion of adic spaces
into pre-adic spaces. -/
instance LocallyOfWeaklyFiniteType.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfWeaklyFiniteType.{u}) :=
  MorphismProperty.RespectsIso.inverseImage
    (chartLocally fun φ ↦ IsTopologicallyFiniteType φ.toRingHom)
    (ObjectProperty.ι PreAdicSpace.isAdic)

/-- **Affinoid morphisms**: for a morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` with `B`
complete and Hausdorff, between pairs whose adic spectra are adic spaces, the morphism
`Spa(B, B⁺) ⟶ Spa(A, A⁺)` induced by `φ` is locally of weakly finite type as soon as the ring
homomorphism of `φ` is topologically of finite type, witnessed over the whole of both spectra.
The converse fails in general (Wedhorn, Remark 8.52). -/
theorem locallyOfWeaklyFiniteType_presentationLimitPreAdicSpaceComap {A : Type u} [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsHuberRing A] {B : Type u} [CommRing B]
    [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B] [CompleteSpace B] [T2Space B]
    [IsHuberRing B] {S : Pair A} {T : Pair B} (P : PairOfDefinition A) (P' : PairOfDefinition B)
    (hP : P.ringOfDefinition ≤ S.plus) (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (hA : PreAdicSpace.isAdic (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)) (φ : Pair.Hom S T)
    (hφ : IsTopologicallyFiniteType φ.toRingHom) :
    LocallyOfWeaklyFiniteType (X := ⟨_, isAdic_presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hsheaf⟩) (Y := ⟨_, hA⟩)
      (ObjectProperty.homMk (presentationLimitPreAdicSpaceComap φ.toRingHom
        φ.continuous_toRingHom φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf)) := by
  rw [locallyOfWeaklyFiniteType_iff_chartLocally, ObjectProperty.homMk_hom]
  exact chartLocally_presentationLimitPreAdicSpaceComap P P' hP hP' hsheaf φ hφ

/-! ### Ascent of finiteness conditions on adic spaces -/

section Ascent

open PairOfDefinition

-- Every chart of a morphism locally of weakly finite type can be upgraded, via rational
-- localization at `{1} / 1`, so that BOTH the target ring `A` and the source ring `B` are complete
-- and Hausdorff, while preserving `IsTopologicallyFiniteType` on rings.
private theorem LocallyOfWeaklyFiniteType.exists_complete_chart {f : X ⟶ Y}
    (hf : LocallyOfWeaklyFiniteType f) (x : X.obj) :
    ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj) (_ : U ≤ (Opens.map f.hom.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (S : Pair A) (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : IsTopologicallyFiniteType φ.toRingHom)
      (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
        (presentationLimitPresheaf P' T.plus))
      (eU : X.obj.restrict U.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem
          hP')
      (eV : Y.obj.restrict V.isOpenEmbedding ≅
        presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          hP),
      X.obj.ofRestrict _ ≫ f.hom =
        eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
          φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫
          eV.inv ≫ Y.obj.ofRestrict _ := by
  classical
  obtain ⟨U, hxU, V, hUV, A, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP', φ, hφ,
    hsheafB, eU, eV, hfac⟩ := (chartLocally_iff f.hom).mp
      ((locallyOfWeaklyFiniteType_iff_chartLocally f).mp hf) x
  -- 1. Form the `{1} / 1` rational localisations of `(A, A⁺)` and `(B, B⁺)`.
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
  -- 2. Establish sheafiness and topological finite type of the base-change morphism `φ₁`.
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
  have hφ₁ : IsTopologicallyFiniteType φ₁.toRingHom := by
    rw [toRingHom_completionLocPairMap]
    exact P.isTopologicallyFiniteType_completionLocMap ({1} : Finset A) 1 L hden P' hφ T' s' L'
      hden' rfl (fun _ ht ↦ Finset.mem_image_of_mem _ ht)
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hT1')
  -- 3. Both `{1} / 1` localisations cover their whole adic spectra, hence induce isomorphisms.
  obtain ⟨eA, heA⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P hP
      ({1} : Finset A) 1 L hden hT1 (fun y ↦ by rw [rationalSubset_singleton_one]; exact y.2)
      hsheafA₁
  obtain ⟨eB, heB⟩ :=
    exists_iso_presentationLimitPreAdicSpaceComap_toCompletionLocHom_of_forall_mem P' hP' T' s' L'
      hden' hT1' (fun y ↦ by
        simp only [T', s', Finset.image_singleton, map_one, rationalSubset_singleton_one]
        exact y.2) hsheafB₁
  -- 4. Conjugate the original chart square by `eA` and `eB`.
  have hcomm := presentationLimitPreAdicSpaceComap_completionLocPairMap_comp P P' hP hP' φ
    hsheafB ({1} : Finset A) 1 L hden L' hden' hsheafA₁ hsheafB₁
  refine ⟨U, hxU, V, hUV, UniformSpace.Completion L, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S₁, P₁, hP₁,
    UniformSpace.Completion L', inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T₁, P₁', hP₁', φ₁, hφ₁, hsheafB₁,
    eU ≪≫ eB.symm, eV ≪≫ eA.symm, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, hfac]
  simp only [Category.assoc]
  congr 1
  have hcomm' : presentationLimitPreAdicSpaceComap φ₁.toRingHom φ₁.continuous_toRingHom
      φ₁.map_mem_plus S₁.isRingOfIntegralElements.isPowerBounded_of_mem
      T₁.isRingOfIntegralElements.isPowerBounded_of_mem hP₁ hP₁' hsheafB₁ ≫ eA.hom =
      eB.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheafB := by
    rw [heA, heB]
    exact hcomm
  rw [← Category.assoc _ eA.hom, hcomm', Category.assoc, Iso.inv_hom_id_assoc]

-- When a morphism `f : Spa(D, D⁺) ⟶ Spa(A, A⁺)` of complete Hausdorff affinoid pre-adic spaces
-- has global-sections homomorphism topologically of finite type and lands inside an open immersion
-- `k : Spa(C, C⁺) ⟶ Spa(A, A⁺)`, lifting `f` across `k` and cancelling on the right produces a
-- ring homomorphism `C →+* D` topologically of finite type.
private theorem exists_isTopologicallyFiniteType_of_range_subset_openImmersion
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A] (P : PairOfDefinition A) (Aplus : Subring A)
    (hApb : ∀ ⦃a⦄, a ∈ Aplus → IsPowerBounded a) (hP : P.ringOfDefinition ≤ Aplus)
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T2Space C] [IsHuberRing C] (PC : PairOfDefinition C) (Cplus : Subring C)
    (hCpb : ∀ ⦃c⦄, c ∈ Cplus → IsPowerBounded c) (hPC : PC.ringOfDefinition ≤ Cplus)
    {D : Type u} [CommRing D] [UniformSpace D] [IsUniformAddGroup D] [IsTopologicalRing D]
    [CompleteSpace D] [T2Space D] [IsHuberRing D] (PD : PairOfDefinition D) (Dplus : Subring D)
    (hDpb : ∀ ⦃d⦄, d ∈ Dplus → IsPowerBounded d) (hPD : PD.ringOfDefinition ≤ Dplus)
    {k : presentationLimitPreAdicSpace PC Cplus hCpb hPC ⟶
      presentationLimitPreAdicSpace P Aplus hApb hP} [IsOpenImmersion k]
    {f : presentationLimitPreAdicSpace PD Dplus hDpb hPD ⟶
      presentationLimitPreAdicSpace P Aplus hApb hP}
    (hrange : Set.range f.base ⊆ Set.range k.base)
    (hf : IsTopologicallyFiniteType
      (presentationLimitHomRingHom P Aplus hApb hP PD Dplus hDpb hPD f)) :
    ∃ β : C →+* D, IsTopologicallyFiniteType β := by
  let g := IsOpenImmersion.lift k f hrange
  have hgk := congrArg (presentationLimitHomRingHom P Aplus hApb hP PD Dplus hDpb hPD)
    (IsOpenImmersion.lift_fac k f hrange)
  rw [presentationLimitHomRingHom_comp P Aplus hApb hP PC Cplus hCpb hPC PD Dplus hDpb hPD] at hgk
  exact ⟨_, IsTopologicallyFiniteType.of_comp (hgk.symm ▸ hf)
    (continuous_presentationLimitHomRingHom P Aplus hApb hP PC Cplus hCpb hPC k)
    (continuous_presentationLimitHomRingHom PC Cplus hCpb hPC PD Dplus hDpb hPD g)⟩

-- Given a morphism `Spa(B, B⁺) ⟶ Spa(A, A⁺)` of complete Hausdorff affinoid spectra induced by a
-- ring homomorphism topologically of finite type, and an open `W` of `Spa(A, A⁺)` isomorphic to a
-- complete Hausdorff `Spa(C, C⁺)`, every point `x` sent into `W` lies in a rational subset
-- `R(T_B / s_B)` whose coordinate ring `B⟨T_B / s_B⟩` receives a homomorphism topologically of
-- finite type from `C`.
private theorem exists_spaBasicOpen_tft_over_complete_open
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A] {S : Pair A} (P : PairOfDefinition A)
    (hP : P.ringOfDefinition ≤ S.plus)
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B] {T : Pair B} (P' : PairOfDefinition B)
    (hP' : P'.ringOfDefinition ≤ T.plus) (φ : Pair.Hom S T)
    (hφ : IsTopologicallyFiniteType φ.toRingHom)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    {C : Type u} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
    [CompleteSpace C] [T2Space C] [IsHuberRing C] {SC : Pair C}
    (PC : PairOfDefinition C) (hPC : PC.ringOfDefinition ≤ SC.plus)
    {W : Opens (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP)}
    (eW : (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP).restrict W.isOpenEmbedding ≅
      presentationLimitPreAdicSpace PC SC.plus
        SC.isRingOfIntegralElements.isPowerBounded_of_mem hPC)
    {x : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP'}
    (hxW : (presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf).base x ∈ W) :
    ∃ (TB : Finset B) (sB : B) (hTB : IsOpen (Ideal.span (TB : Set B) : Set B)),
      x ∈ spaBasicOpen T.plus TB sB ∧
      letI hden := P'.hasDenominatorPower_of_isOpen_span TB sB (Localization.Away sB) hTB
      letI := P'.locUniformSpace TB sB (Localization.Away sB) hden
      letI := P'.isUniformAddGroup_locUniformSpace TB sB (Localization.Away sB) hden
      letI := P'.isTopologicalRing_locUniformSpace TB sB (Localization.Away sB) hden
      ∃ β : C →+* UniformSpace.Completion (Localization.Away sB),
        IsTopologicallyFiniteType β := by
  let q := presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf
  -- Choose a rational neighbourhood `R(TB / sB) ⊆ q⁻¹(W)` of `x`.
  obtain ⟨R, hR, hxR, hRW⟩ := Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens T.plus)
    ((Opens.mem_map (f := q.base) (U := W)).mpr hxW)
  obtain ⟨TB, sB, hTB, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hR
  refine ⟨TB, sB, hTB, hxR, ?_⟩
  let LD := Localization.Away sB
  have hdenD := P'.hasDenominatorPower_of_isOpen_span TB sB LD hTB
  let _ := P'.locUniformSpace TB sB LD hdenD
  have _ := P'.isUniformAddGroup_locUniformSpace TB sB LD hdenD
  have _ := P'.isTopologicalRing_locUniformSpace TB sB LD hdenD
  have _ := P'.isHuberRing_completion_locTopology TB sB LD hdenD
  have hTpb := T.isRingOfIntegralElements.isPowerBounded_of_mem
  have hsheafD := isSheaf_presentationLimitPresheaf_completionLocalization P' T.plus hTpb hP'
    TB sB LD hdenD hTB hsheaf
  let PD := P'.completionLocalization TB sB LD hdenD
  let Dplus := P'.completedPlusSubring T.plus TB sB LD hdenD
  have hDpb := P'.isPowerBounded_of_mem_completedPlusSubring T.plus hTpb TB sB LD hdenD
  have hPD := P'.completionLocalization_ringOfDefinition_le_completedPlusSubring T.plus hP' TB sB
    LD hdenD
  let ιD := presentationLimitPreAdicSpaceComap (P'.toCompletionLoc TB sB LD hdenD)
    (P'.continuous_toCompletionLoc TB sB LD hdenD)
    (fun _ hb ↦ P'.toCompletionLoc_mem_completedPlusSubring T.plus TB sB LD hdenD hb)
    hTpb hDpb hP' hPD hsheafD
  -- Lift `ιD ≫ q : Spa(B⟨TB/sB⟩) ⟶ Spa(A)` across the open immersion `Spa(C) ≅ W ↪ Spa(A)`.
  let MA := presentationLimitPreAdicSpace P S.plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem hP
  let k := eW.inv ≫ MA.ofRestrict W.isOpenEmbedding
  have : IsOpenImmersion k := IsOpenImmersion.comp _ _
  refine exists_isTopologicallyFiniteType_of_range_subset_openImmersion P S.plus _ hP PC SC.plus _
    hPC PD Dplus hDpb hPD (k := k) (f := ιD ≫ q) ?_ ?_
  · rintro _ ⟨z, rfl⟩
    have hzR : ιD.base z ∈ (spaBasicOpen T.plus TB sB : Set (spa T.plus)) := by
      rw [← range_presentationLimitPreAdicSpaceComap_toCompletionLoc_base P' T.plus TB sB LD hdenD
        hTpb hP' hsheafD]
      exact ⟨z, rfl⟩
    let w : MA.restrict W.isOpenEmbedding := ⟨q.base (ιD.base z), hRW hzR⟩
    refine ⟨eW.hom.base w, ?_⟩
    have hw : (eW.hom ≫ eW.inv).base w = w := by simp
    exact congrArg (MA.ofRestrict W.isOpenEmbedding).base hw
  · rw [presentationLimitHomRingHom_comp P S.plus _ hP P' T.plus _ hP' PD Dplus hDpb hPD,
      presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap,
      presentationLimitHomRingHom_presentationLimitPreAdicSpaceComap]
    exact (P'.isTopologicallyFiniteType_toCompletionLoc TB sB LD hdenD
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTB)).comp hφ

-- Common chart-refinement step ascending an isomorphism-invariant affinoid property `Q` along a
-- morphism locally of weakly finite type whenever `Q` ascends along homomorphisms topologically of
-- finite type between complete Hausdorff Huber rings.
private theorem LocallyOfWeaklyFiniteType.forall_exists_mem_propOpens {f : X ⟶ Y}
    (hf : LocallyOfWeaklyFiniteType f) (Q : ObjectProperty PreAdicSpace.{u})
    [Q.IsClosedUnderIsomorphisms] (hbasis : Opens.IsBasis (Y.obj.propOpens Q))
    (hQ : ∀ {Z : PreAdicSpace.{u}}, Q Z →
      ∃ (C : Type u) (_ : CommRing C) (_ : UniformSpace C) (_ : IsUniformAddGroup C)
        (_ : IsTopologicalRing C) (_ : CompleteSpace C) (_ : T2Space C) (_ : IsHuberRing C)
        (SC : Pair C) (PC : PairOfDefinition C) (hPC : PC.ringOfDefinition ≤ SC.plus),
        Nonempty (Z ≅ presentationLimitPreAdicSpace PC SC.plus
          SC.isRingOfIntegralElements.isPowerBounded_of_mem hPC) ∧
        ∀ {D : Type u} [CommRing D] [UniformSpace D] [IsUniformAddGroup D] [IsTopologicalRing D]
          [CompleteSpace D] [T2Space D] [IsHuberRing D] {β : C →+* D},
          IsTopologicallyFiniteType β →
          ∀ (SD : Pair D) (PD : PairOfDefinition D) (hPD : PD.ringOfDefinition ≤ SD.plus),
            Q (presentationLimitPreAdicSpace PD SD.plus
              SD.isRingOfIntegralElements.isPowerBounded_of_mem hPD)) :
    ∀ x : X.obj, ∃ U ∈ X.obj.propOpens Q, x ∈ U := by
  intro x
  obtain ⟨U, hxU, V, -, A, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, hsheaf, eU, eV, -⟩ := hf.exists_complete_chart x
  let q := presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom φ.map_mem_plus
    S.isRingOfIntegralElements.isPowerBounded_of_mem
    T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf
  obtain ⟨W, hW, hxW⟩ := exists_mem_propOpens_of_iso Q eV.symm
    (exists_mem_propOpens_restrict V.isOpenEmbedding Q hbasis) (q.base (eU.hom.base ⟨x, hxU⟩))
  obtain ⟨C, _, _, _, _, _, _, _, SC, PC, hPC, ⟨eW⟩, htft⟩ := hQ ((mem_propOpens_iff _).mp hW)
  obtain ⟨TB, sB, hTB, hxR, hβ⟩ := exists_spaBasicOpen_tft_over_complete_open P hP P' hP' φ hφ
    hsheaf PC hPC eW hxW
  have hden := P'.hasDenominatorPower_of_isOpen_span TB sB (Localization.Away sB) hTB
  let _ := P'.locUniformSpace TB sB (Localization.Away sB) hden
  have _ := P'.isUniformAddGroup_locUniformSpace TB sB (Localization.Away sB) hden
  have _ := P'.isTopologicalRing_locUniformSpace TB sB (Localization.Away sB) hden
  have _ := P'.isHuberRing_completion_locTopology TB sB (Localization.Away sB) hden
  obtain ⟨β, hβtft⟩ := hβ
  have hRmem : spaBasicOpen T.plus TB sB ∈
      (presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP').propOpens Q :=
    spaBasicOpen_mem_propOpens P' T.plus TB sB _ hden
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP' hTB Q (htft hβtft _ _ _)
  have hUmem := (map_hom_base_mem_propOpens_iff Q eU).mpr hRmem
  exact ⟨U.isOpenEmbedding.isOpenMap.functor.obj ((Opens.map eU.hom.base).obj _),
    (mem_propOpens_restrict_iff X.obj U.isOpenEmbedding Q _).mp hUmem, ⟨x, hxU⟩, hxR, rfl⟩

/-- **Locally noetherian structure ascends along morphisms locally of weakly finite type**
(Huber 1994, §3; Wedhorn, Proposition 6.35 and Definition 8.48): if `f : X ⟶ Y` is locally of
weakly finite type and `Y` is locally noetherian, then `X` is locally noetherian. -/
theorem IsLocallyNoetherian.of_locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfWeaklyFiniteType f) (hY : Y.IsLocallyNoetherian) : X.IsLocallyNoetherian := by
  refine isLocallyNoetherian_iff.mpr <|
    hf.forall_exists_mem_propOpens isNoetherianAffinoid hY.isBasis_noetherianAffinoidOpens
      fun hZ ↦ ?_
  obtain ⟨C, _, _, _, _, _, _, _, _, SC, PC, hPC, eZ⟩ := (isNoetherianAffinoid_iff _).mp hZ
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, SC, PC, hPC, eZ, fun hβ SD PD hPD ↦ ?_⟩
  have := IsNoetherianType.of_isTopologicallyFiniteType hβ
  exact isNoetherianAffinoid_presentationLimitPreAdicSpace SD PD hPD

/-- **Locally noetherian structure ascends along morphisms locally of finite type.** -/
theorem IsLocallyNoetherian.of_locallyOfFiniteType {f : X ⟶ Y}
    (hf : PreAdicSpace.LocallyOfFiniteType f.hom) (hY : Y.IsLocallyNoetherian) :
    X.IsLocallyNoetherian :=
  hY.of_locallyOfWeaklyFiniteType hf.locallyOfWeaklyFiniteType

/-- **Being locally of Huber's standing class ascends along morphisms locally of weakly finite
type** (Huber 1996, (1.1.1) and §1.2): if `f : X ⟶ Y` is locally of weakly finite type and `Y` is
locally of Huber's standing class, then `X` is locally of Huber's standing class. -/
theorem IsLocallyHuberStandard.of_locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfWeaklyFiniteType f) (hY : Y.IsLocallyHuberStandard) :
    X.IsLocallyHuberStandard := by
  refine isLocallyHuberStandard_iff.mpr <|
    hf.forall_exists_mem_propOpens isHuberStandardAffinoid hY.isBasis_huberStandardAffinoidOpens
      fun hZ ↦ ?_
  obtain ⟨C, _, _, _, _, _, _, _, _, SC, PC, hPC, eZ⟩ := (isHuberStandardAffinoid_iff _).mp hZ
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, SC, PC, hPC, eZ, fun hβ SD PD hPD ↦ ?_⟩
  have := IsHuberStandard.of_isTopologicallyFiniteType hβ
  exact isHuberStandardAffinoid_presentationLimitPreAdicSpace SD PD hPD

/-- **Being locally of Huber's standing class ascends along morphisms locally of finite type.** -/
theorem IsLocallyHuberStandard.of_locallyOfFiniteType {f : X ⟶ Y}
    (hf : PreAdicSpace.LocallyOfFiniteType f.hom) (hY : Y.IsLocallyHuberStandard) :
    X.IsLocallyHuberStandard :=
  hY.of_locallyOfWeaklyFiniteType hf.locallyOfWeaklyFiniteType

end Ascent

end AdicSpace

end TauCeti
