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

A morphism `f : X ⟶ Y` of adic spaces is *locally of finite presentation* (Huber 1996, (1.1.1) and
Definition 1.2.1(v); Wedhorn, Remark 6.37 and Definition 8.48) when every `x ∈ X` admits complete
Hausdorff affinoid charts `X|_U ≅ Spa(B, B⁺)` and `Y|_V ≅ Spa(A, A⁺)` with `f(U) ⊆ V`, induced by
`φ : (A, A⁺) → (B, B⁺)` such that `IsHuberStandard A`, `φ.IsTopologicallyFiniteType`, and
`DiscreteTopology A → φ.toRingHom.FinitePresentation`. Since `IsHuberStandard` ascends along
`φ`, `X` is unconditionally locally of Huber's standing class and locally noetherian.

## Main definitions

* `TauCeti.AdicSpace.LocallyOfFinitePresentationAt`: the pointwise chart condition at `x : X.obj`.
* `TauCeti.AdicSpace.LocallyOfFinitePresentation`: morphisms locally of finite presentation.

## Main results

* `LocallyOfFinitePresentation.locallyOfFiniteType`, `.locallyOfPlusWeaklyFiniteType`,
  `.locallyOfWeaklyFiniteType`, `.isAdic`: implications down Huber's hierarchy.
* `LocallyOfFinitePresentation.isLocallyHuberStandard_source`, `.isLocallyNoetherian_source`:
  unconditional source regularity.
* `LocallyOfFinitePresentation.exists_openImmersion_chart`,
  `locallyOfFinitePresentationAt_of_openImmersion_sq`,
  `locallyOfFinitePresentation_iff_forall_exists_openImmersion_chart`: open-immersion charts.
* `LocallyOfFinitePresentation.of_isOpenImmersion`, `.id`, `locallyOfFinitePresentation_id_iff`,
  `.of_isEmpty`, `.respectsIso`: open immersions, identities, empty sources, and iso-invariance.
* `LocallyOfFinitePresentation.exists_openImmersion_over_rationalLocalization`, `.comp`,
  `.isStableUnderComposition`: rational chart refinement and composition closure.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), (1.1.1) and Definition 1.2.1(v).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37 and Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti

open Huber ValuationSpectrum

universe u

namespace AdicSpace

open PreAdicSpace CompleteAffinoidOpen

variable {X Y Z : AdicSpace.{u}}

/-- **Pointwise chart condition for `TauCeti.AdicSpace.LocallyOfFinitePresentation`** at
`x : X.obj`: there exist open neighbourhoods `U ⊆ X` of `x` and `V ⊆ Y` with `f(U) ⊆ V`, complete
Hausdorff Huber pairs `(A, A⁺)` and `(B, B⁺)` with `A` in Huber's standing class
(`IsHuberStandard A`), a morphism `φ : (A, A⁺) → (B, B⁺)` topologically of finite type whose ring
map is algebraically of finite presentation whenever `A` is discrete, and isomorphisms
`X|_U ≅ Spa(B, B⁺)` and `Y|_V ≅ Spa(A, A⁺)` identifying `f|_U` with the morphism induced by `φ`. -/
def LocallyOfFinitePresentationAt (f : X ⟶ Y) (x : X.obj) : Prop :=
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
      (presentationLimitPresheaf P' T.plus)) (eU : X.obj.restrict U.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P' T.plus T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
    (eV : Y.obj.restrict V.isOpenEmbedding ≅
      presentationLimitPreAdicSpace P S.plus S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
    X.obj.ofRestrict _ ≫ f.hom =
      eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
        φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫ Y.obj.ofRestrict _

/-- **Morphisms locally of finite presentation** (Huber 1996, (1.1.1) and Definition 1.2.1(v)):
a morphism `f : X ⟶ Y` of adic spaces is *locally of finite presentation* when
`LocallyOfFinitePresentationAt f x` holds at every point `x ∈ X`, i.e., locally on complete
Hausdorff affinoid charts `X|_U ≅ Spa(B, B⁺)` and `Y|_V ≅ Spa(A, A⁺)`, `f` is induced by a
morphism of Huber pairs `φ : (A, A⁺) → (B, B⁺)` topologically of finite type with
`IsHuberStandard A` and `DiscreteTopology A → φ.toRingHom.FinitePresentation`. -/
def LocallyOfFinitePresentation : MorphismProperty AdicSpace.{u} := fun _ _ f ↦
  ∀ x, LocallyOfFinitePresentationAt f x

/-- Unfolding lemma for `TauCeti.AdicSpace.LocallyOfFinitePresentation`. -/
theorem locallyOfFinitePresentation_iff (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔ ∀ x : X.obj, LocallyOfFinitePresentationAt f x := Iff.rfl

/-- **A morphism locally of finite presentation is locally of finite type** (Huber 1996, §1.2):
forgetting `IsHuberStandard A` and the discrete finite-presentation condition leaves a finite-type
chart around every point. -/
theorem LocallyOfFinitePresentation.locallyOfFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfFiniteType f := by
  refine (locallyOfFiniteType_iff_chartLocally f).mpr <| (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hxU, V, hUV, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, -, hsheaf, eU, eV, hfac⟩ := hf x
  exact ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, B,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, hφ, hsheaf, eU, eV, hfac⟩

/-- **A morphism locally of finite presentation is locally of +weakly finite type.** -/
theorem LocallyOfFinitePresentation.locallyOfPlusWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfPlusWeaklyFiniteType f :=
  hf.locallyOfFiniteType.locallyOfPlusWeaklyFiniteType

/-- **A morphism locally of finite presentation is locally of weakly finite type.** -/
theorem LocallyOfFinitePresentation.locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfWeaklyFiniteType f :=
  hf.locallyOfFiniteType.locallyOfWeaklyFiniteType

/-- **A morphism locally of finite presentation is adic** (Huber 1996, §1.2). -/
theorem LocallyOfFinitePresentation.isAdic {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : IsAdic f := hf.locallyOfFiniteType.isAdic

/-- **Unconditional source regularity**: if `f : X ⟶ Y` is locally of finite presentation, then the
source `X` is locally of Huber's standing class (`X.IsLocallyHuberStandard`), with no hypothesis on
`Y` (each chart target ring satisfies `IsHuberStandard A`, which ascends to `B`). -/
theorem LocallyOfFinitePresentation.isLocallyHuberStandard_source {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : X.IsLocallyHuberStandard := by
  rw [isLocallyHuberStandard_iff]; intro x
  obtain ⟨U, hxU, _, -, A, _, _, _, _, _, _, _, _, _, _, _, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, -, -, eU, -, -⟩ := hf x
  have : IsHuberStandard B := .of_isTopologicallyFiniteType hφ.isTopologicallyFiniteType_toRingHom
  refine ⟨U, (mem_propOpens_iff _).mpr ((isHuberStandardAffinoid_iff _).mpr ?_), hxU⟩
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T, P', hP', ⟨eU⟩⟩

/-- **Unconditional locally noetherian source**: if `f : X ⟶ Y` is locally of finite presentation,
then `X` is locally noetherian (`X.IsLocallyNoetherian`), with no hypothesis on `Y`. -/
theorem LocallyOfFinitePresentation.isLocallyNoetherian_source {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : X.IsLocallyNoetherian :=
  hf.isLocallyHuberStandard_source.isLocallyNoetherian

/-- **Open-immersion chart extraction for `LocallyOfFinitePresentation`**: if `f : X ⟶ Y` is
locally of finite presentation, every `x ∈ X` admits complete affinoid opens `CY` of `Y` (with
`IsHuberStandard CY.Ring`) and `CX` of `X` covering `x`, together with a morphism
`φ : CY.pair → CX.pair` topologically of finite type and conditionally algebraically of finite
presentation when `CY.Ring` is discrete, making the open-immersion square commute. -/
theorem LocallyOfFinitePresentation.exists_openImmersion_chart {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (x : X.obj) :
    ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
      (_ : IsHuberStandard CY.Ring) (φ : Pair.Hom CY.pair CX.pair) (_ : φ.IsTopologicallyFiniteType)
      (_ : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) (b₀ : CX.space),
      CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom := by
  obtain ⟨U, hxU, V, -, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, hfp, hsheafB, eU, eV, hfac⟩ := hf x
  have hsheafA := isSheaf_of_restrict_iso P hP eV
  exact ⟨ofRestrictIso S P hP hsheafA eV, ofRestrictIso T P' hP' hsheafB eU,
    (inferInstance : IsHuberStandard A), φ, hφ, hfp, eU.hom.base ⟨x, hxU⟩,
    ofRestrictIso_hom_base .., ofRestrictIso_pairComap_comp_hom _ _ _ _ _ _ _ _ _ _ φ hfac⟩

/-- **Pointwise open-immersion chart construction for `LocallyOfFinitePresentationAt`**: a
commuting open-immersion square `CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom` covering `x ∈ X`
with `IsHuberStandard CY.Ring`, `φ.IsTopologicallyFiniteType`, and
`DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation` witnesses
`LocallyOfFinitePresentationAt f x`. -/
theorem locallyOfFinitePresentationAt_of_openImmersion_sq {f : X ⟶ Y} {x : X.obj}
    (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj) [IsHuberStandard CY.Ring]
    (φ : Pair.Hom CY.pair CX.pair) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) {b₀ : CX.space}
    (hb₀ : CX.hom.base b₀ = x) (hsq : CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom) :
    LocallyOfFinitePresentationAt f x := by
  let U : Opens X.obj := ⟨Set.range CX.hom.base, CX.hom.isOpenEmbedding.isOpen_range⟩
  let V : Opens Y.obj := ⟨Set.range CY.hom.base, CY.hom.isOpenEmbedding.isOpen_range⟩
  have hUV : U ≤ (Opens.map f.hom.base).obj V := fun _ ⟨b, hb⟩ ↦
    hb ▸ ⟨(CY.pairComap CX φ).base b, CY.pairComap_comp_hom_base CX φ hsq b⟩
  let eU := IsOpenImmersion.isoOfRangeEq (X.obj.ofRestrict U.isOpenEmbedding) CX.hom
    (Opens.set_range_inclusion' U)
  let eV := IsOpenImmersion.isoOfRangeEq (Y.obj.ofRestrict V.isOpenEmbedding) CY.hom
    (Opens.set_range_inclusion' V)
  have heU := IsOpenImmersion.isoOfRangeEq_hom_comp (X.obj.ofRestrict U.isOpenEmbedding) CX.hom
    (Opens.set_range_inclusion' U)
  have heV := IsOpenImmersion.isoOfRangeEq_inv_comp (Y.obj.ofRestrict V.isOpenEmbedding) CY.hom
    (Opens.set_range_inclusion' V)
  refine ⟨U, ⟨b₀, hb₀⟩, V, hUV, CY.Ring, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, CY.pair, CY.pairOfDefinition,
    CY.le_plus, CX.Ring, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, CX.pair, CX.pairOfDefinition, CX.le_plus, φ, hφ,
    hfp, CX.isSheaf, eU, eV, ?_⟩
  rw [← presentationLimitPreAdicSpacePairComap_def]
  calc
    X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom
      = eU.hom ≫ (CX.hom ≫ f.hom) := by rw [← Category.assoc, heU]
    _ = eU.hom ≫ (CY.pairComap CX φ ≫ CY.hom) := by rw [hsq]
    _ = eU.hom ≫ CY.pairComap CX φ ≫ eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding := by rw [heV]

/-- **Open-immersion chart characterisation of `LocallyOfFinitePresentation`**: a morphism
`f : X ⟶ Y` of adic spaces is locally of finite presentation if and only if every `x ∈ X` is
covered by a commuting open-immersion square between complete affinoid opens with
`IsHuberStandard CY.Ring`, `φ.IsTopologicallyFiniteType`, and
`DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation`. -/
theorem locallyOfFinitePresentation_iff_forall_exists_openImmersion_chart (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      ∀ x : X.obj, ∃ (CY : CompleteAffinoidOpen Y.obj) (CX : CompleteAffinoidOpen X.obj)
        (_ : IsHuberStandard CY.Ring) (φ : Pair.Hom CY.pair CX.pair)
        (_ : φ.IsTopologicallyFiniteType)
        (_ : DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) (b₀ : CX.space),
        CX.hom.base b₀ = x ∧ CY.pairComap CX φ ≫ CY.hom = CX.hom ≫ f.hom :=
  ⟨fun hf x ↦ hf.exists_openImmersion_chart x, fun h x ↦ by
    obtain ⟨CY, CX, _, φ, hφ, hfp, b₀, hb₀, hsq⟩ := h x
    exact locallyOfFinitePresentationAt_of_openImmersion_sq CY CX φ hφ hfp hb₀ hsq⟩

/-- **Open immersions into targets locally of Huber's standing class are locally of finite
presentation**: the standing-class hypothesis `hY : Y.IsLocallyHuberStandard` is necessary because
target charts in `LocallyOfFinitePresentation` must lie in Huber's standing class. -/
theorem LocallyOfFinitePresentation.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] (hY : Y.IsLocallyHuberStandard) :
    LocallyOfFinitePresentation f := fun x ↦ by
  let O : Opens Y.obj := ⟨Set.range f.hom.base, f.hom.isOpenEmbedding.isOpen_range⟩
  have hfxO : f.hom.base x ∈ O := ⟨x, rfl⟩
  obtain ⟨V, hV, hfxV, hVO⟩ := Opens.isBasis_iff_nbhd.mp hY.isBasis_huberStandardAffinoidOpens hfxO
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isHuberStandardAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheafA := isSheaf_of_restrict_iso P hP eV
  let U : Opens X.obj := (Opens.map f.hom.base).obj V
  have hrange : Set.range (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom).base =
      Set.range (Y.obj.ofRestrict V.isOpenEmbedding).base := by
    ext y; refine ⟨?_, ?_⟩
    · rintro ⟨u, rfl⟩
      rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply,
        PreAdicSpace.ofRestrict_base]
      exact ⟨⟨f.hom.base u.val, u.property⟩, by rw [PreAdicSpace.ofRestrict_base]; rfl⟩
    · rintro ⟨v, rfl⟩; let v' : ↥V := v; obtain ⟨x', hx'⟩ := hVO v'.property
      let u' : X.obj.restrict U.isOpenEmbedding := ⟨x', Opens.mem_map.mpr (hx'.symm ▸ v'.property)⟩
      refine ⟨u', ?_⟩
      rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply,
        PreAdicSpace.ofRestrict_base, PreAdicSpace.ofRestrict_base]; exact hx'
  let eUV := IsOpenImmersion.isoOfRangeEq
    (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom) (Y.obj.ofRestrict V.isOpenEmbedding) hrange
  have heUV := IsOpenImmersion.isoOfRangeEq_hom_comp
    (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom) (Y.obj.ofRestrict V.isOpenEmbedding) hrange
  let eU := eUV ≪≫ eV
  refine ⟨U, hfxV, V, le_rfl, A, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP, A, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, S,
      P, hP, Pair.Hom.id S, Pair.Hom.isTopologicallyFiniteType_id S,
      fun _ ↦ by simpa [Pair.Hom.toRingHom_id] using RingHom.FinitePresentation.id A,
      hsheafA, eU, eV, ?_⟩
  have hid : presentationLimitPreAdicSpaceComap (Pair.Hom.id S).toRingHom
      (Pair.Hom.id S).continuous_toRingHom (Pair.Hom.id S).map_mem_plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP hP hsheafA = 𝟙 _ :=
    (presentationLimitPreAdicSpacePairComap_def ..).symm.trans
      (presentationLimitPreAdicSpacePairComap_id P hP hsheafA)
  rw [hid]
  calc
    X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom
      = eUV.hom ≫ Y.obj.ofRestrict V.isOpenEmbedding := heUV.symm
    _ = eU.hom ≫ 𝟙 _ ≫ eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding := by
        simp only [eU, Iso.trans_hom, Category.assoc, Iso.hom_inv_id_assoc, Category.id_comp]

/-- **Identities on adic spaces locally of Huber's standing class are locally of finite
presentation** (the standing-class hypothesis `hX : X.IsLocallyHuberStandard` is necessary; see
`locallyOfFinitePresentation_id_iff`). -/
theorem LocallyOfFinitePresentation.id (hX : X.IsLocallyHuberStandard) :
    LocallyOfFinitePresentation (𝟙 X) := LocallyOfFinitePresentation.of_isOpenImmersion (𝟙 X) hX

/-- **Characterisation of when an identity morphism is locally of finite presentation**:
`LocallyOfFinitePresentation (𝟙 X) ↔ X.IsLocallyHuberStandard`. -/
theorem locallyOfFinitePresentation_id_iff :
    LocallyOfFinitePresentation (𝟙 X) ↔ X.IsLocallyHuberStandard :=
  ⟨fun h ↦ h.isLocallyHuberStandard_source, LocallyOfFinitePresentation.id⟩

/-- **Every morphism out of an empty adic space is locally of finite presentation** (vacuously,
with no hypothesis on the target). -/
theorem LocallyOfFinitePresentation.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] :
    LocallyOfFinitePresentation f := fun x ↦ isEmptyElim x

/-- **Being locally of finite presentation is invariant under isomorphisms** of the source and of
the target. -/
instance LocallyOfFinitePresentation.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) where
  precomp {X' X Y} i _ f hf x' := by
    let e : X'.obj ≅ X.obj := (ObjectProperty.ι _).mapIso (asIso i)
    have hi : i.hom = e.hom := by simp [e]
    obtain ⟨CY, CX, _, φ, hφ, hfp, b₀, hb₀, hsq⟩ := hf.exists_openImmersion_chart (e.hom.base x')
    have hb₀' : (CX.compOpenImmersion e.inv).hom.base b₀ = x' := by
      have he := congrArg (fun m : X'.obj ⟶ X'.obj ↦ m.base x') e.hom_inv_id
      rw [PreAdicSpace.comp_base, TopCat.coe_comp, Function.comp_apply] at he
      rw [compOpenImmersion_hom_base, hb₀]; exact he.trans (by simp)
    refine locallyOfFinitePresentationAt_of_openImmersion_sq CY (CX.compOpenImmersion e.inv)
      φ hφ hfp hb₀' ?_
    rw [pairComap_compOpenImmersion_right_eq_comp_iff, ObjectProperty.FullSubcategory.comp_hom,
      hi, Iso.inv_hom_id_assoc]
    exact hsq
  postcomp {X Y Y'} i _ f hf x := by
    let e : Y.obj ≅ Y'.obj := (ObjectProperty.ι _).mapIso (asIso i)
    have hi : i.hom = e.hom := by simp [e]
    obtain ⟨CY, CX, hStd, φ, hφ, hfp, b₀, hb₀, hsq⟩ := hf.exists_openImmersion_chart x
    have : IsHuberStandard (CY.compOpenImmersion e.hom).Ring := hStd
    refine locallyOfFinitePresentationAt_of_openImmersion_sq (CY.compOpenImmersion e.hom) CX
      φ hφ hfp hb₀ ?_
    rw [pairComap_compOpenImmersion_left_comp_hom, ObjectProperty.FullSubcategory.comp_hom,
      hi, ← Category.assoc, hsq, Category.assoc]

/-- Transfer of topological finite type and conditional algebraic finite presentation along a
chart factorisation `φ.comp ψ = (CX₀.rationalLocalizationHom TC sC hTC).comp χ` obtained after
rationally shrinking the source chart `CX₀`. -/
theorem isTopologicallyFiniteType_and_finitePresentation_of_comp_rationalLocalization
    {X₀ Y₀ Z₀ : PreAdicSpace.{u}} {CZ : CompleteAffinoidOpen Z₀} [IsHuberStandard CZ.Ring]
    {CY : CompleteAffinoidOpen Y₀} {CX₀ : CompleteAffinoidOpen X₀} {TC : Finset CX₀.Ring}
    {sC : CX₀.Ring} {hTC : IsOpen (Ideal.span (TC : Set CX₀.Ring) : Set CX₀.Ring)}
    {ψ : Pair.Hom CZ.pair CY.pair} (hψ : ψ.IsTopologicallyFiniteType)
    {χ : Pair.Hom CZ.pair CX₀.pair} (hχ : χ.IsTopologicallyFiniteType)
    (hχ_fp : DiscreteTopology CZ.Ring → χ.toRingHom.FinitePresentation)
    {φ : Pair.Hom CY.pair (CX₀.rationalLocalization TC sC hTC).pair}
    (hcomp : φ.comp ψ = (CX₀.rationalLocalizationHom TC sC hTC).comp χ) :
    φ.IsTopologicallyFiniteType ∧ (DiscreteTopology CY.Ring → φ.toRingHom.FinitePresentation) := by
  have hφ_tft : φ.IsTopologicallyFiniteType :=
    .of_comp (hcomp ▸ (CX₀.isTopologicallyFiniteType_rationalLocalizationHom TC sC hTC).comp hχ)
  refine ⟨hφ_tft, fun _ ↦ hψ.isTopologicallyFiniteType_toRingHom.finitePresentation_of_comp
    hφ_tft.isTopologicallyFiniteType_toRingHom fun hDiscA ↦ ?_⟩
  have : DiscreteTopology CX₀.Ring := hχ.isTopologicallyFiniteType_toRingHom.discreteTopology
  rw [← Pair.Hom.toRingHom_comp, hcomp, Pair.Hom.toRingHom_comp]
  exact (CX₀.finitePresentation_rationalLocalizationHom TC sC hTC).comp (hχ_fp hDiscA)

/-- **Chart refinement over a prescribed target open for `LocallyOfFinitePresentation`**: given
`f : X ⟶ Y` locally of finite presentation, an arbitrary complete affinoid open `CY` of `Y` (not
assumed to satisfy `IsHuberStandard`), and a point `x ∈ X` whose image `f(x)` is hit by
`a₀ ∈ CY.space`, there exists a rational localisation `CY₁ = CY.rationalLocalization TA sA hTA`
containing `a₀` such that `IsHuberStandard CY₁.Ring` and a complete affinoid open `CX` of `X`
covering `x` over `CY₁` via a finite-presentation Huber-pair morphism `β`. -/
theorem LocallyOfFinitePresentation.exists_openImmersion_over_rationalLocalization {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (CY : CompleteAffinoidOpen Y.obj) (x : X.obj)
    {a₀ : CY.space} (ha₀ : CY.hom.base a₀ = f.hom.base x) : ∃ (TA : Finset CY.Ring) (sA : CY.Ring)
      (hTA : IsOpen (Ideal.span (TA : Set CY.Ring) : Set CY.Ring)),
      a₀ ∈ spaBasicOpen CY.pair.plus TA sA ∧
      let CY₁ := CY.rationalLocalization TA sA hTA; IsHuberStandard CY₁.Ring ∧
      ∃ (CX : CompleteAffinoidOpen X.obj) (β : Pair.Hom CY₁.pair CX.pair)
        (_ : β.IsTopologicallyFiniteType)
        (_ : DiscreteTopology CY₁.Ring → β.toRingHom.FinitePresentation) (c₀ : CX.space),
        CX.hom.base c₀ = x ∧ CY₁.pairComap CX β ≫ CY₁.hom = CX.hom ≫ f.hom := by
  obtain ⟨CY', CX₀, _, φ', hφ', hfp', c₀₀, hc₀₀, hsq'⟩ := hf.exists_openImmersion_chart x
  have had₀ : CY'.hom.base ((CY'.pairComap CX₀ φ').base c₀₀) = CY.hom.base a₀ := by
    rw [CY'.pairComap_comp_hom_base CX₀ φ' hsq' c₀₀, hc₀₀, ha₀]
  obtain ⟨TA', sA', hTA', -, a'₁, α₀, ha'₁, hsq_α₀⟩ :=
    exists_ofRationalLocalization_lift CY'.pairOfDefinition CY'.le_plus CY'.isSheaf CY'.hom CY
      (𝟙 Y.obj) (by rw [Category.comp_id]; exact had₀)
  let CY'₁ := CY'.rationalLocalization TA' sA' hTA'
  have had₁ : (CY.hom ≫ 𝟙 Y.obj).base a₀ = CY'₁.hom.base a'₁ := by
    rw [Category.comp_id]; exact had₀.symm.trans ha'₁.symm
  obtain ⟨TA, sA, hTA, ha₀R, a₁, α₁, ha₁, hsq_α₁⟩ :=
    exists_ofRationalLocalization_lift CY.pairOfDefinition CY.le_plus CY.isSheaf CY.hom CY'₁
      (𝟙 Y.obj) had₁
  let CY₁ := CY.rationalLocalization TA sA hTA
  have hα₁α₀ : α₁.comp α₀ = CY.rationalLocalizationHom TA sA hTA := CY.pairComap_injective CY₁ <| by
    rw [CY.pairComap_comp CY'₁ CY₁, ← cancel_mono CY.hom, Category.assoc, hsq_α₀,
      Category.comp_id, hsq_α₁, Category.comp_id, ofRationalLocalization_hom]
  have hα₁_tft : α₁.IsTopologicallyFiniteType :=
    .of_comp (hα₁α₀ ▸ CY.isTopologicallyFiniteType_rationalLocalizationHom TA sA hTA)
  let ψ₀ := α₁.comp (CY'.rationalLocalizationHom TA' sA' hTA')
  have hψ₀_tft := hα₁_tft.comp (CY'.isTopologicallyFiniteType_rationalLocalizationHom TA' sA' hTA')
  have hsq_ψ₀ : CY'.pairComap CY₁ ψ₀ ≫ CY'.hom = CY₁.hom ≫ 𝟙 Y.obj :=
    (CY'.pairComap_comp_rationalLocalizationHom_comp_hom CY₁ α₁).trans hsq_α₁
  obtain ⟨TC, sC, hTC, β, c₁, hc₁, hsq, hβψ₀⟩ :=
    exists_rationalLocalization_lift_sq CY' CY₁ CX₀ ψ₀ φ'
      (ha₁.trans ha₀) hc₀₀ hsq_ψ₀ (by simpa using hsq')
  obtain ⟨hβ_tft, hβ_fp⟩ :=
    isTopologicallyFiniteType_and_finitePresentation_of_comp_rationalLocalization
      hψ₀_tft hφ' hfp' hβψ₀
  exact ⟨TA, sA, hTA, ha₀R,
    .of_isTopologicallyFiniteType hψ₀_tft.isTopologicallyFiniteType_toRingHom,
    CX₀.rationalLocalization TC sC hTC, β, hβ_tft, hβ_fp, c₁, hc₁, hsq⟩

/-- **Composition of morphisms locally of finite presentation** (Huber 1996, §1.2): if `f : X ⟶ Y`
and `g : Y ⟶ Z` are locally of finite presentation, then `f ≫ g` is locally of finite
presentation. -/
theorem LocallyOfFinitePresentation.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyOfFinitePresentation f) (hg : LocallyOfFinitePresentation g) :
    LocallyOfFinitePresentation (f ≫ g) := fun x ↦ by
  obtain ⟨CZ, CY, _, ψ, hψ, hψ_fp, b₀, hb₀, hsq_g⟩ := hg.exists_openImmersion_chart (f.hom.base x)
  obtain ⟨TB, sB, hTB, -, -, CX, β, hβ, hβ_fp, c₀, hc₀, hsq_f⟩ :=
    hf.exists_openImmersion_over_rationalLocalization CY x hb₀
  let ψ₁ := (CY.rationalLocalizationHom TB sB hTB).comp ψ
  have hψ₁_tft := (CY.isTopologicallyFiniteType_rationalLocalizationHom TB sB hTB).comp hψ
  have hfp : DiscreteTopology CZ.Ring → (β.comp ψ₁).toRingHom.FinitePresentation := fun hDiscA ↦ by
    have : DiscreteTopology CY.Ring := hψ.isTopologicallyFiniteType_toRingHom.discreteTopology
    have : DiscreteTopology (CY.rationalLocalization TB sB hTB).Ring :=
      hψ₁_tft.isTopologicallyFiniteType_toRingHom.discreteTopology
    rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp]
    exact (hβ_fp inferInstance).comp
      ((CY.finitePresentation_rationalLocalizationHom TB sB hTB).comp (hψ_fp hDiscA))
  refine locallyOfFinitePresentationAt_of_openImmersion_sq CZ CX (β.comp ψ₁)
    (hβ.comp hψ₁_tft) hfp hc₀ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom]
  exact CZ.pairComap_comp_rationalLocalization_sq CY hTB CX ψ β hsq_g hsq_f

/-- `LocallyOfFinitePresentation` is stable under composition. -/
instance LocallyOfFinitePresentation.isStableUnderComposition :
    LocallyOfFinitePresentation.{u}.IsStableUnderComposition where comp_mem _ _ hf hg := hf.comp hg

end AdicSpace

end TauCeti
