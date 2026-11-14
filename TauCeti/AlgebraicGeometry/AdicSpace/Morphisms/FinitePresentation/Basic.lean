/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Morphisms.FiniteType
public import TauCeti.AlgebraicGeometry.AdicSpace.PreAdicSpace.LocallyHuberStandard

import TauCeti.RingTheory.Huber.LocalizationTopology.Discrete
import TauCeti.RingTheory.Huber.LocalizationTopology.Noetherian
import TauCeti.RingTheory.Huber.NoetherianType.TopologicallyFiniteType
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Cancel
import TauCeti.RingTheory.Huber.TopologicallyFiniteType.Comp

/-!
# Morphisms of adic spaces locally of finite presentation

Huber's theory of unramified, smooth, and étale morphisms of adic spaces (Huber 1996, §§1.2–1.7)
takes place over adic spaces locally of Huber's standing class (`TauCeti.Huber.IsHuberStandard`,
Huber 1996, (1.1.1)): Huber rings that are finite type over a noetherian ring of definition, are
strongly noetherian Tate rings, or carry the discrete topology. Within this class, the first two
alternatives force every algebra topologically of finite type to be noetherian, whereas the discrete
alternative allows non-noetherian discrete bases where `IsTopologicallyFiniteType` reduces to
`RingHom.FiniteType` (`TauCeti.Huber.isTopologicallyFiniteType_iff_finiteType`) without controlling
the kernel of presentations.

Following Huber (1996, Definition 1.2.1(ii)), a morphism `f : X ⟶ Y` of adic spaces is *locally of
finite presentation* (`TauCeti.AdicSpace.LocallyOfFinitePresentation`) when every point `x` of `X`
has an open neighbourhood `U`, mapped by `f` into an open `V` of `Y`, together with isomorphisms
`U ≅ Spa(B, B⁺)` and `V ≅ Spa(A, A⁺)` for complete Hausdorff Huber pairs with `A` in Huber's
standing class, under which `f` restricted to `U → V` is induced by a morphism of Huber pairs
`φ : (A, A⁺) → (B, B⁺)` topologically of finite type satisfying `φ.toRingHom.FinitePresentation`
whenever `A` is discrete. Completeness and Hausdorffness of `A` ensure that `A` is canonically and
topologically isomorphic to `𝒪_Y(V)`, making both `IsHuberStandard A` and `DiscreteTopology A`
intrinsic properties of the open affinoid `V`.

The standing-class dichotomy
(`TauCeti.Huber.IsHuberStandard.discreteTopology_or_isNoetherianRing_of_isTopologicallyFiniteType`)
governs chart refinements: for any homomorphism `γ : A →+* C` topologically of finite type out of a
ring `A` in Huber's standing class, either `A` is discrete or `C` is noetherian. Consequently,
whenever a refined target `A₁` becomes discrete while `A` was not discrete, `A₁` is noetherian and
finite type over `A₁` upgrades automatically to finite presentation
(`RingHom.FinitePresentation.of_finiteType`); when `A` is already discrete, both `A` and `B` are
discrete and completed rational localization agrees with algebraic `Localization.Away`
(`TauCeti.Huber.PairOfDefinition.finitePresentation_toCompletionLoc_of_discreteTopology`).

## Main definitions

* `TauCeti.AdicSpace.LocallyOfFinitePresentation`: morphisms of adic spaces locally of finite
  presentation in the sense of Huber (1996, Definition 1.2.1(ii)).

## Main results

* `TauCeti.AdicSpace.LocallyOfFinitePresentation.locallyOfFiniteType`,
  `TauCeti.AdicSpace.LocallyOfFinitePresentation.isLocallyHuberStandard_source`,
  `TauCeti.AdicSpace.LocallyOfFinitePresentation.isLocallyNoetherian_source`: placement in Huber's
  finiteness hierarchy and unconditional ascent of `IsLocallyHuberStandard` and
  `IsLocallyNoetherian` to the source.
* `TauCeti.AdicSpace.LocallyOfFinitePresentation.of_isOpenImmersion`,
  `TauCeti.AdicSpace.locallyOfFinitePresentation_id_iff`,
  `TauCeti.AdicSpace.LocallyOfFinitePresentation.respectsIso`: open immersions into spaces locally
  of Huber's standing class are locally of finite presentation, `𝟙 X` is locally of finite
  presentation if and only if `X.IsLocallyHuberStandard`, and invariance under isomorphisms.
* `TauCeti.AdicSpace.LocallyOfFinitePresentation.exists_openImmersion_chart`,
  `TauCeti.AdicSpace.exists_locallyOfFinitePresentation_chart_of_openImmersion_sq`,
  `TauCeti.AdicSpace.LocallyOfFinitePresentation.exists_openImmersion_over_rationalLocalization`:
  open-immersion chart extraction and refinement over any complete Hausdorff sheafy affinoid open
  immersion into the target.
* `TauCeti.AdicSpace.LocallyOfFinitePresentation.comp`,
  `TauCeti.AdicSpace.LocallyOfFinitePresentation.isStableUnderComposition`: closure under
  composition.

## References

* R. Huber, *Étale cohomology of rigid analytic varieties and adic spaces*, Aspects of
  Mathematics E30 (1996), (1.1.1) and Definition 1.2.1(ii).
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Remark 6.37 and Definition 8.48.
-/

public section

open CategoryTheory TopologicalSpace Topology

namespace TauCeti.AdicSpace

open Huber Huber.PairOfDefinition PreAdicSpace ValuationSpectrum

universe u

/-- **Morphisms locally of finite presentation** (Huber 1996, Definition 1.2.1(ii)): a morphism
`f : X ⟶ Y` of adic spaces is *locally of finite presentation* when every point `x : X.obj` has open
neighbourhoods `U` of `x` and `V` of `f(x)` with `U ≤ f⁻¹(V)`, complete Hausdorff Huber pairs
`S = (A, A⁺)` and `T = (B, B⁺)` with `A` in Huber's standing class (`IsHuberStandard A`) and
`Spa(B, B⁺)` sheafy, isomorphisms `X|_U ≅ Spa(B, B⁺)` and `Y|_V ≅ Spa(A, A⁺)`, and a morphism of
Huber pairs `φ : S → T` topologically of finite type satisfying `φ.toRingHom.FinitePresentation`
whenever `A` is discrete, inducing `f` from `U` to `V`. -/
def LocallyOfFinitePresentation : MorphismProperty AdicSpace.{u} := fun X Y f ↦
  ∀ x : X.obj,
    ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj) (_ : U ≤ (Opens.map f.hom.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (_ : IsHuberStandard A) (S : Pair A) (P : PairOfDefinition A)
      (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : φ.IsTopologicallyFiniteType)
      (_ : DiscreteTopology A → φ.toRingHom.FinitePresentation)
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
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
          Y.obj.ofRestrict _

variable {X Y Z : AdicSpace.{u}}

/-- Unfolding lemma for `TauCeti.AdicSpace.LocallyOfFinitePresentation`. -/
theorem locallyOfFinitePresentation_iff (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      ∀ x : X.obj,
        ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj) (_ : U ≤ (Opens.map f.hom.base).obj V)
          (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
          (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
          (_ : IsHuberStandard A) (S : Pair A) (P : PairOfDefinition A)
          (hP : P.ringOfDefinition ≤ S.plus)
          (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
          (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
          (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
          (φ : Pair.Hom S T) (_ : φ.IsTopologicallyFiniteType)
          (_ : DiscreteTopology A → φ.toRingHom.FinitePresentation)
          (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
            (presentationLimitPresheaf P' T.plus))
          (eU : X.obj.restrict U.isOpenEmbedding ≅
            presentationLimitPreAdicSpace P' T.plus
              T.isRingOfIntegralElements.isPowerBounded_of_mem hP')
          (eV : Y.obj.restrict V.isOpenEmbedding ≅
            presentationLimitPreAdicSpace P S.plus
              S.isRingOfIntegralElements.isPowerBounded_of_mem hP),
          X.obj.ofRestrict _ ≫ f.hom =
            eU.hom ≫ presentationLimitPreAdicSpaceComap φ.toRingHom φ.continuous_toRingHom
              φ.map_mem_plus S.isRingOfIntegralElements.isPowerBounded_of_mem
              T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
              Y.obj.ofRestrict _ :=
  Iff.rfl

/-! ### Hierarchy and source regularity -/

/-- **Every morphism locally of finite presentation is locally of finite type** (Huber 1996,
Definition 1.2.1). -/
theorem LocallyOfFinitePresentation.locallyOfFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfFiniteType f := by
  refine (locallyOfFiniteType_iff_chartLocally f).mpr <| (chartLocally_iff _).mpr fun x ↦ ?_
  obtain ⟨U, hxU, V, hUV, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, -, hsheaf, eU, eV, hfac⟩ := hf x
  exact ⟨U, hxU, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, hφ, hsheaf, eU, eV, hfac⟩

/-- **A morphism locally of finite presentation is locally of +weakly finite type.** -/
theorem LocallyOfFinitePresentation.locallyOfPlusWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfPlusWeaklyFiniteType f :=
  hf.locallyOfFiniteType.locallyOfPlusWeaklyFiniteType

/-- **A morphism locally of finite presentation is locally of weakly finite type.** -/
theorem LocallyOfFinitePresentation.locallyOfWeaklyFiniteType {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : LocallyOfWeaklyFiniteType f :=
  hf.locallyOfFiniteType.locallyOfWeaklyFiniteType

/-- **A morphism locally of finite presentation is adic.** -/
theorem LocallyOfFinitePresentation.isAdic {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : IsAdic f :=
  hf.locallyOfFiniteType.isAdic

/-- **The source of a morphism locally of finite presentation is locally of Huber's standing
class**: each chart expresses an open neighbourhood of `x : X.obj` as `Spa(B, B⁺)` for a complete
Hausdorff Huber pair topologically of finite type over a ring `A` in Huber's standing class, so `B`
belongs to Huber's standing class (`IsHuberStandard.of_isTopologicallyFiniteType`). -/
theorem LocallyOfFinitePresentation.isLocallyHuberStandard_source {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : X.IsLocallyHuberStandard := by
  rw [isLocallyHuberStandard_iff]
  intro x
  obtain ⟨U, hxU, _, -, A, _, _, _, _, _, _, _, _, _, _, _, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, -, -, eU, -, -⟩ := hf x
  have : IsHuberStandard B := .of_isTopologicallyFiniteType hφ.isTopologicallyFiniteType_toRingHom
  refine ⟨U, (mem_propOpens_iff _).mpr ((isHuberStandardAffinoid_iff _).mpr ?_), hxU⟩
  exact ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, T, P', hP', ⟨eU⟩⟩

/-- The source of a morphism locally of finite presentation is locally noetherian. -/
theorem LocallyOfFinitePresentation.isLocallyNoetherian_source {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) : X.IsLocallyNoetherian :=
  hf.isLocallyHuberStandard_source.isLocallyNoetherian

/-! ### Identities, open immersions, and isomorphisms -/

/-- **Open immersions into adic spaces locally of Huber's standing class are locally of finite
presentation** (Huber 1996, §1.2). -/
theorem LocallyOfFinitePresentation.of_isOpenImmersion (f : X ⟶ Y)
    [PreAdicSpace.IsOpenImmersion f.hom] (hY : Y.IsLocallyHuberStandard) :
    LocallyOfFinitePresentation f := by
  intro x
  let O : Opens Y.obj := ⟨Set.range f.hom.base, f.hom.isOpenEmbedding.isOpen_range⟩
  have hfxO : f.hom.base x ∈ O := ⟨x, rfl⟩
  obtain ⟨V, hV, hfxV, hVO⟩ :=
    Opens.isBasis_iff_nbhd.mp hY.isBasis_huberStandardAffinoidOpens hfxO
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, ⟨eV⟩⟩ :=
    (isHuberStandardAffinoid_iff _).mp ((mem_propOpens_iff _).mp hV)
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy)
  let U : Opens X.obj := (Opens.map f.hom.base).obj V
  have hrange :
      Set.range (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom).base =
        Set.range (Y.obj.ofRestrict V.isOpenEmbedding).base := by
    ext y
    constructor
    · rintro ⟨⟨x', hx'⟩, rfl⟩
      exact ⟨⟨f.hom.base x', hx'⟩, rfl⟩
    · rintro ⟨⟨y', hy'⟩, rfl⟩
      obtain ⟨x', rfl⟩ := hVO hy'
      exact ⟨⟨x', hy'⟩, rfl⟩
  let eUV := PreAdicSpace.IsOpenImmersion.isoOfRangeEq
    (X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom) (Y.obj.ofRestrict V.isOpenEmbedding) hrange
  have heUV :
      eUV.hom ≫ Y.obj.ofRestrict V.isOpenEmbedding =
        X.obj.ofRestrict U.isOpenEmbedding ≫ f.hom :=
    PreAdicSpace.IsOpenImmersion.isoOfRangeEq_hom_comp _ _ hrange
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
  simp [eU, heUV]

/-- The identity morphism on an adic space locally of Huber's standing class is locally of finite
presentation. -/
theorem LocallyOfFinitePresentation.of_id (hX : X.IsLocallyHuberStandard) :
    LocallyOfFinitePresentation (𝟙 X) :=
  LocallyOfFinitePresentation.of_isOpenImmersion (𝟙 X) hX

/-- **Characterization of identities locally of finite presentation**: `𝟙 X` is locally of finite
presentation if and only if `X` is locally of Huber's standing class. -/
theorem locallyOfFinitePresentation_id_iff :
    LocallyOfFinitePresentation (𝟙 X) ↔ X.IsLocallyHuberStandard :=
  ⟨fun h ↦ h.isLocallyHuberStandard_source, LocallyOfFinitePresentation.of_id⟩

/-- Every morphism out of an empty adic space is locally of finite presentation. -/
theorem LocallyOfFinitePresentation.of_isEmpty (f : X ⟶ Y) [IsEmpty X.obj] :
    LocallyOfFinitePresentation f :=
  fun x ↦ isEmptyElim x

/-- **Being locally of finite presentation is invariant under isomorphisms** of source and target.
-/
instance LocallyOfFinitePresentation.respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFinitePresentation.{u}) where
  precomp {X' X Y} i _ f hf x' := by
    let e : X'.obj ≅ X.obj := (ObjectProperty.ι _).mapIso (asIso i)
    obtain ⟨U, hxU, V, hUV, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P',
      hP', φ, hφ, hfp, hsheaf, eU, eV, hfac⟩ := hf (e.hom.base x')
    refine ⟨(Opens.map e.hom.base).obj U, hxU, V, fun y hy ↦ hUV hy, A, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, S, P, hP, B, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, T, P', hP', φ, hφ, hfp, hsheaf,
      (PreAdicSpace.restrictIso e.symm U).symm ≪≫ eU, eV, ?_⟩
    rw [ObjectProperty.FullSubcategory.comp_hom (f := i) (g := f),
      show i.hom = e.hom from rfl, Iso.trans_hom, Iso.symm_hom, Category.assoc, ← hfac,
      PreAdicSpace.restrictIso_inv_ofRestrict_assoc]
    rfl
  postcomp {X Y Y'} i _ f hf x := by
    let e : Y.obj ≅ Y'.obj := (ObjectProperty.ι _).mapIso (asIso i)
    obtain ⟨U, hxU, V, hUV, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P',
      hP', φ, hφ, hfp, hsheaf, eU, eV, hfac⟩ := hf x
    have key := Opens.map_hom_obj_map_inv_obj (PreAdicSpace.forgetToTop.mapIso e) V
    simp only [Functor.mapIso_hom, Functor.mapIso_inv, PreAdicSpace.forgetToTop_map] at key
    refine ⟨U, hxU, (Opens.map e.inv.base).obj V, fun y hy ↦ ?_, A, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, S,
      P, hP, B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, T, P', hP', φ, hφ, hfp, hsheaf, eU,
      (PreAdicSpace.restrictIso e V).symm ≪≫ eV, ?_⟩
    · have hy' : f.hom.base y ∈ (Opens.map e.hom.base).obj ((Opens.map e.inv.base).obj V) :=
        key.symm ▸ hUV hy
      exact hy'
    · rw [ObjectProperty.FullSubcategory.comp_hom (f := f) (g := i),
        show i.hom = e.hom from rfl, reassoc_of% hfac]
      simp

/-! ### Open-immersion chart refinement and composition -/

section OpenImmersionCharts

/-- Extract an open-immersion chart around `x : X.obj` from `LocallyOfFinitePresentation f` with
complete Hausdorff source and target Huber rings and sheafy adic spectra. -/
theorem LocallyOfFinitePresentation.exists_openImmersion_chart {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) (x : X.obj) :
    ∃ (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (_ : IsHuberStandard A) (S : Pair A) (P : PairOfDefinition A)
      (hP : P.ringOfDefinition ≤ S.plus)
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
      (_ : DiscreteTopology A → φ.toRingHom.FinitePresentation)
      (b₀ : presentationLimitPreAdicSpace P' T.plus
        T.isRingOfIntegralElements.isPowerBounded_of_mem hP'),
      kX.base b₀ = x ∧
      presentationLimitPreAdicSpacePairComap P P' hP hP' hsheafB φ ≫ kY = kX ≫ f.hom := by
  obtain ⟨U, hxU, V, -, A, _, _, _, _, _, _, _, _, S, P, hP, B, _, _, _, _, _, _, _, T, P', hP',
    φ, hφ, hfp, hsheafB, eU, eV, hfac⟩ := hf x
  have hsheafA : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa S.plus))
      (presentationLimitPresheaf P S.plus) :=
    ObjectProperty.prop_of_iso isSheafy eV (isSheafy_restrict _ Y.property.isSheafy)
  let kX := eU.inv ≫ X.obj.ofRestrict U.isOpenEmbedding
  let kY := eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding
  have hkX : PreAdicSpace.IsOpenImmersion kX := PreAdicSpace.IsOpenImmersion.comp _ _
  have hkY : PreAdicSpace.IsOpenImmersion kY := PreAdicSpace.IsOpenImmersion.comp _ _
  let b₀ := eU.hom.base ⟨x, hxU⟩
  refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, S, P, hP, hsheafA,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', hsheafB, kX, hkX, kY, hkY, φ, hφ, hfp, b₀, ?_, ?_⟩
  · have hb : (eU.hom ≫ eU.inv).base ⟨x, hxU⟩ = ⟨x, hxU⟩ := by
      simp
      rfl
    exact congrArg (X.obj.ofRestrict U.isOpenEmbedding).base hb
  · dsimp only [kX, kY]
    rw [presentationLimitPreAdicSpacePairComap_def, Category.assoc, hfac, Iso.inv_hom_id_assoc]

/-- Turn a point-level open-immersion chart square covering `x : X.obj` into a chart witness for
`LocallyOfFinitePresentation f` at `x`. -/
theorem exists_locallyOfFinitePresentation_chart_of_openImmersion_sq {f : X ⟶ Y} {x : X.obj}
    {A : Type u} [CommRing A] [UniformSpace A] [IsUniformAddGroup A] [IsTopologicalRing A]
    [CompleteSpace A] [T2Space A] [IsHuberRing A] [IsHuberStandard A]
    {S : Pair A} {P : PairOfDefinition A} (hP : P.ringOfDefinition ≤ S.plus)
    {B : Type u} [CommRing B] [UniformSpace B] [IsUniformAddGroup B] [IsTopologicalRing B]
    [CompleteSpace B] [T2Space B] [IsHuberRing B]
    {T : Pair B} {P' : PairOfDefinition B} (hP' : P'.ringOfDefinition ≤ T.plus)
    (hsheaf : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa T.plus))
      (presentationLimitPresheaf P' T.plus))
    (kX : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP' ⟶ X.obj)
    [PreAdicSpace.IsOpenImmersion kX]
    (kY : presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP ⟶ Y.obj)
    [PreAdicSpace.IsOpenImmersion kY]
    (φ : Pair.Hom S T) (hφ : φ.IsTopologicallyFiniteType)
    (hfp : DiscreteTopology A → φ.toRingHom.FinitePresentation)
    {b₀ : presentationLimitPreAdicSpace P' T.plus
      T.isRingOfIntegralElements.isPowerBounded_of_mem hP'}
    (hb₀ : kX.base b₀ = x)
    (hsq : presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ ≫ kY = kX ≫ f.hom) :
    ∃ (U : Opens X.obj) (_ : x ∈ U) (V : Opens Y.obj) (_ : U ≤ (Opens.map f.hom.base).obj V)
      (A : Type u) (_ : CommRing A) (_ : UniformSpace A) (_ : IsUniformAddGroup A)
      (_ : IsTopologicalRing A) (_ : CompleteSpace A) (_ : T2Space A) (_ : IsHuberRing A)
      (_ : IsHuberStandard A) (S : Pair A) (P : PairOfDefinition A)
      (hP : P.ringOfDefinition ≤ S.plus)
      (B : Type u) (_ : CommRing B) (_ : UniformSpace B) (_ : IsUniformAddGroup B)
      (_ : IsTopologicalRing B) (_ : CompleteSpace B) (_ : T2Space B) (_ : IsHuberRing B)
      (T : Pair B) (P' : PairOfDefinition B) (hP' : P'.ringOfDefinition ≤ T.plus)
      (φ : Pair.Hom S T) (_ : φ.IsTopologicallyFiniteType)
      (_ : DiscreteTopology A → φ.toRingHom.FinitePresentation)
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
          T.isRingOfIntegralElements.isPowerBounded_of_mem hP hP' hsheaf ≫ eV.inv ≫
          Y.obj.ofRestrict _ := by
  let U : Opens X.obj := ⟨Set.range kX.base, kX.isOpenEmbedding.isOpen_range⟩
  let V : Opens Y.obj := ⟨Set.range kY.base, kY.isOpenEmbedding.isOpen_range⟩
  have hUV : U ≤ (Opens.map f.hom.base).obj V := by
    rintro _ ⟨b, rfl⟩
    refine ⟨(presentationLimitPreAdicSpacePairComap P P' hP hP' hsheaf φ).base b, ?_⟩
    exact congrArg (fun m ↦ m.base b) hsq
  let eU := PreAdicSpace.IsOpenImmersion.isoOfRangeEq (X.obj.ofRestrict U.isOpenEmbedding) kX
    (Opens.set_range_inclusion' U)
  let eV := PreAdicSpace.IsOpenImmersion.isoOfRangeEq (Y.obj.ofRestrict V.isOpenEmbedding) kY
    (Opens.set_range_inclusion' V)
  have heU : eU.hom ≫ kX = X.obj.ofRestrict U.isOpenEmbedding :=
    PreAdicSpace.IsOpenImmersion.isoOfRangeEq_hom_comp _ _ _
  have heV : eV.inv ≫ Y.obj.ofRestrict V.isOpenEmbedding = kY :=
    PreAdicSpace.IsOpenImmersion.isoOfRangeEq_inv_comp _ _ _
  refine ⟨U, ⟨b₀, hb₀⟩, V, hUV, A, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, S, P, hP,
    B, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, T, P', hP', φ, hφ, hfp, hsheaf, eU, eV, ?_⟩
  rw [← presentationLimitPreAdicSpacePairComap_def, heV,
    ← Category.assoc eU.hom, Category.assoc eU.hom, hsq, ← Category.assoc, heU]

/-- **Refinement of a finitely presented morphism over a given complete Hausdorff target affinoid**:
let `f : X ⟶ Y` be locally of finite presentation, let `kY : Spa(A, A⁺) ⟶ Y.obj` be an open
immersion from a complete Hausdorff Huber pair with sheafy structure presheaf (with no standing-
class assumption imposed a priori on `A`), and let `f.hom.base x = kY.base a₀`. Then `a₀` has a
rational open neighbourhood `R(TA / sA)` in `Spa(A, A⁺)` whose completed localization `A₁` belongs
to Huber's standing class, and `x` has a complete Hausdorff sheafy affinoid open neighbourhood
`kX : Spa(C, C⁺) ⟶ X.obj` factoring `kX ≫ f.hom` through `R(TA / sA)` via a morphism of Huber pairs
`β : (A₁, A₁⁺) → (C, C⁺)` that is topologically of finite type and satisfies
`DiscreteTopology A₁ → β.toRingHom.FinitePresentation`. -/
theorem LocallyOfFinitePresentation.exists_openImmersion_over_rationalLocalization {f : X ⟶ Y}
    (hf : LocallyOfFinitePresentation f) {A : Type u} [CommRing A] [UniformSpace A]
    [IsUniformAddGroup A] [IsTopologicalRing A] [CompleteSpace A] [T2Space A] [IsHuberRing A]
    {S : Pair A} (P : PairOfDefinition A) (hP : P.ringOfDefinition ≤ S.plus)
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
      IsHuberStandard (UniformSpace.Completion LA) ∧
      ∃ (C : Type u) (_ : CommRing C) (_ : UniformSpace C) (_ : IsUniformAddGroup C)
        (_ : IsTopologicalRing C) (_ : CompleteSpace C) (_ : T2Space C) (_ : IsHuberRing C)
        (U : Pair C) (PC : PairOfDefinition C) (hPC : PC.ringOfDefinition ≤ U.plus)
        (hsheafC : Presheaf.IsSheaf (Opens.grothendieckTopology ↥(spa U.plus))
          (presentationLimitPresheaf PC U.plus))
        (kX : presentationLimitPreAdicSpace PC U.plus
          U.isRingOfIntegralElements.isPowerBounded_of_mem hPC ⟶ X.obj)
        (_ : PreAdicSpace.IsOpenImmersion kX)
        (β : Pair.Hom S₁ U) (_ : β.IsTopologicallyFiniteType)
        (_ : DiscreteTopology (UniformSpace.Completion LA) → β.toRingHom.FinitePresentation)
        (c₀ : presentationLimitPreAdicSpace PC U.plus
          U.isRingOfIntegralElements.isPowerBounded_of_mem hPC),
        kX.base c₀ = x ∧
        presentationLimitPreAdicSpacePairComap P₁ PC hP₁ hPC hsheafC β ≫
          presentationLimitPreAdicSpacePairComap P P₁ hP hP₁ hsheafA₁
            (P.toCompletionLocHom S hP TA sA LA hdenA) ≫ kY = kX ≫ f.hom := by
  classical
  -- 1. Choose a complete chart `(kX₀ : Spa(C₀) ⟶ X, kY' : Spa(A') ⟶ Y, φ' : A' → C₀)`.
  obtain ⟨A', _, _, _, _, _, _, _, _, S', P', hP', hsheafA', C₀, _, _, _, _, _, _, _, U₀, PC₀,
    hPC₀, hsheafC₀, kX₀, hkX₀, kY', hkY', φ', hφ', hfp', c₀₀, hc₀₀, hsq'⟩ :=
    hf.exists_openImmersion_chart x
  -- 2. Shrink `Spa(A')` around `a'₀ := Spa(φ')(c₀₀)` to a rational open `R(TA' / sA')` mapping
  -- into `Set.range kY.base`, and base-change `φ'` along it.
  let a'₀ := (presentationLimitPreAdicSpacePairComap P' PC₀ hP' hPC₀ hsheafC₀ φ').base c₀₀
  let OA' : Opens (presentationLimitPreAdicSpace P' S'.plus
      S'.isRingOfIntegralElements.isPowerBounded_of_mem hP') :=
    ⟨kY'.base ⁻¹' Set.range kY.base, kY.isOpenEmbedding.isOpen_range.preimage kY'.base.hom.2⟩
  have ha'₀O : a'₀ ∈ OA' := by
    refine ⟨a₀, ?_⟩
    have h1 := congrArg (fun m ↦ m.base c₀₀) hsq'
    simpa [a'₀, hc₀₀, ha₀] using h1.symm
  obtain ⟨RA', hRA', ha'₀R, hRA'O⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens S'.plus) ha'₀O
  obtain ⟨TA', sA', hTA', rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRA'
  let TC₀ : Finset C₀ := TA'.image φ'.toRingHom
  let sC₀ : C₀ := φ'.toRingHom sA'
  have hTC₀ : IsOpen (Ideal.span (TC₀ : Set C₀) : Set C₀) := by
    rw [Finset.coe_image, ← Ideal.map_span]
    exact hφ'.isTopologicallyFiniteType_toRingHom.isOpen_map hTA'
  let LA' := Localization.Away sA'
  let LC₀ := Localization.Away sC₀
  have hdenA' := P'.hasDenominatorPower_of_isOpen_span TA' sA' LA' hTA'
  have hdenC₀ := PC₀.hasDenominatorPower_of_isOpen_span TC₀ sC₀ LC₀ hTC₀
  let _ := P'.locUniformSpace TA' sA' LA' hdenA'
  have _ := P'.isUniformAddGroup_locUniformSpace TA' sA' LA' hdenA'
  have _ := P'.isTopologicalRing_locUniformSpace TA' sA' LA' hdenA'
  have _ := P'.isHuberRing_completion_locTopology TA' sA' LA' hdenA'
  let _ := PC₀.locUniformSpace TC₀ sC₀ LC₀ hdenC₀
  have _ := PC₀.isUniformAddGroup_locUniformSpace TC₀ sC₀ LC₀ hdenC₀
  have _ := PC₀.isTopologicalRing_locUniformSpace TC₀ sC₀ LC₀ hdenC₀
  have _ := PC₀.isHuberRing_completion_locTopology TC₀ sC₀ LC₀ hdenC₀
  let S'₁ := P'.rationalLocalizationPair S' hP' TA' sA' LA' hdenA'
  let P'₁ := P'.completionLocalization TA' sA' LA' hdenA'
  let U₁ := PC₀.rationalLocalizationPair U₀ hPC₀ TC₀ sC₀ LC₀ hdenC₀
  let PC₁ := PC₀.completionLocalization TC₀ sC₀ LC₀ hdenC₀
  have hP'₁ : P'₁.ringOfDefinition ≤ S'₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact P'.completionLocalization_ringOfDefinition_le_completedPlusSubring S'.plus hP' TA' sA'
      LA' hdenA'
  have hPC₁ : PC₁.ringOfDefinition ≤ U₁.plus := by
    rw [rationalLocalizationPair_plus]
    exact PC₀.completionLocalization_ringOfDefinition_le_completedPlusSubring U₀.plus hPC₀ TC₀ sC₀
      LC₀ hdenC₀
  have hsheafA'₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P' S' hP' TA' sA'
    LA' hdenA' hTA' hsheafA'
  have hsheafC₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair PC₀ U₀ hPC₀ TC₀ sC₀
    LC₀ hdenC₀ hTC₀ hsheafC₀
  let φ'₁ := P'.completionLocPairMap S' hP' TA' sA' LA' hdenA' PC₀ U₀ hPC₀ φ' TC₀ sC₀ LC₀ hdenC₀
    rfl (fun _ ht ↦ Finset.mem_image_of_mem _ ht)
  have hTA'_ins : IsOpen (Ideal.span (insert sA' (TA' : Set A')) : Set A') :=
    Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTA'
  have hTC₀_ins : IsOpen (Ideal.span (insert sC₀ (TC₀ : Set C₀)) : Set C₀) :=
    Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTC₀
  have hStdA'₁ : IsHuberStandard (UniformSpace.Completion LA') :=
    isHuberStandard_completion_locTopology_of_isHuberStandard P' hTA'_ins LA' hdenA'
  have hφ'₁ : φ'₁.IsTopologicallyFiniteType :=
    P'.isTopologicallyFiniteType_completionLocPairMap S' hP' TA' sA' LA' hdenA' PC₀ U₀ hPC₀ φ'
      TC₀ sC₀ LC₀ hdenC₀ rfl (fun _ ht ↦ Finset.mem_image_of_mem _ ht) hφ' hTC₀_ins
  have hfp'₁ :
      DiscreteTopology (UniformSpace.Completion LA') → φ'₁.toRingHom.FinitePresentation := by
    rw [show φ'₁.toRingHom = _ from toRingHom_completionLocPairMap ..]
    exact P'.finitePresentation_completionLocMap_of_discreteTopology TA' sA' hTA'_ins LA' hdenA'
      PC₀ hφ'.isTopologicallyFiniteType_toRingHom hfp' TC₀ sC₀ LC₀ hdenC₀ rfl
      (fun _ ht ↦ Finset.mem_image_of_mem _ ht) hTC₀_ins
  let ιA' := presentationLimitPreAdicSpacePairComap P' P'₁ hP' hP'₁ hsheafA'₁
    (P'.toCompletionLocHom S' hP' TA' sA' LA' hdenA')
  have hιA'_imm : PreAdicSpace.IsOpenImmersion ιA' := by
    rw [show ιA' = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom P' hP' TA' sA' LA'
      hdenA' hTA' hsheafA'₁
  have hιA'_range : Set.range ιA'.base = (spaBasicOpen S'.plus TA' sA' : Set (spa S'.plus)) := by
    rw [show ιA' = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base P' hP' TA' sA' LA'
      hdenA' hsheafA'₁
  let ιC₀ := presentationLimitPreAdicSpacePairComap PC₀ PC₁ hPC₀ hPC₁ hsheafC₁
    (PC₀.toCompletionLocHom U₀ hPC₀ TC₀ sC₀ LC₀ hdenC₀)
  have hιC₀_imm : PreAdicSpace.IsOpenImmersion ιC₀ := by
    rw [show ιC₀ = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom PC₀ hPC₀ TC₀ sC₀
      LC₀ hdenC₀ hTC₀ hsheafC₁
  have hιC₀_range : Set.range ιC₀.base = (spaBasicOpen U₀.plus TC₀ sC₀ : Set (spa U₀.plus)) := by
    rw [show ιC₀ = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base PC₀ hPC₀ TC₀ sC₀ LC₀
      hdenC₀ hsheafC₁
  let kX₁ := ιC₀ ≫ kX₀
  let kY'₁ := ιA' ≫ kY'
  have hkX₁_imm : PreAdicSpace.IsOpenImmersion kX₁ := PreAdicSpace.IsOpenImmersion.comp ιC₀ kX₀
  have hkY'₁_imm : PreAdicSpace.IsOpenImmersion kY'₁ := PreAdicSpace.IsOpenImmersion.comp ιA' kY'
  have hc₀₀R : (c₀₀ : spa U₀.plus) ∈ (spaBasicOpen U₀.plus TC₀ sC₀ : Set (spa U₀.plus)) := by
    have hmem : (φ'.spaComap c₀₀).1 ∈ rationalSubset S'.plus TA' sA' := by
      have ha' := mem_spaBasicOpen.mp ha'₀R
      dsimp only [a'₀] at ha'
      rwa [presentationLimitPreAdicSpacePairComap_base_apply P' PC₀ hP' hPC₀ hsheafC₀ φ' c₀₀]
        at ha'
    have hpre := Set.ext_iff.mp (φ'.spaComap_preimage_rationalSubset TA' sA') c₀₀
    exact mem_spaBasicOpen.mpr (hpre.mp hmem)
  obtain ⟨c₁₀, hc₁₀⟩ : (c₀₀ : spa U₀.plus) ∈ Set.range ιC₀.base := hιC₀_range.symm ▸ hc₀₀R
  have hc₁₀_x : kX₁.base c₁₀ = x := by
    simpa [kX₁, ← hc₀₀] using congrArg kX₀.base hc₁₀
  have hsq'₁ :
      presentationLimitPreAdicSpacePairComap P'₁ PC₁ hP'₁ hPC₁ hsheafC₁ φ'₁ ≫ kY'₁ =
        kX₁ ≫ f.hom := by
    have hcomm := presentationLimitPreAdicSpaceComap_completionLocPairMap_comp P' PC₀ hP' hPC₀ φ'
      hsheafC₀ TA' sA' LA' hdenA' LC₀ hdenC₀ hsheafA'₁ hsheafC₁
    dsimp only [kY'₁, kX₁, ιA', ιC₀, φ'₁, TC₀, sC₀]
    rw [presentationLimitPreAdicSpacePairComap_def, presentationLimitPreAdicSpacePairComap_def,
      presentationLimitPreAdicSpacePairComap_def, ← Category.assoc, hcomm, Category.assoc]
    rw [← presentationLimitPreAdicSpacePairComap_def P' PC₀ hP' hPC₀ hsheafC₀ φ', hsq',
      Category.assoc]
  have hrange₀ : Set.range kY'₁.base ⊆ Set.range kY.base := by
    rintro _ ⟨z, rfl⟩
    have hz : (ιA'.base z : spa S'.plus) ∈ (spaBasicOpen S'.plus TA' sA' : Set (spa S'.plus)) :=
      hιA'_range ▸ ⟨z, rfl⟩
    exact hRA'O hz
  let l₀ := PreAdicSpace.IsOpenImmersion.lift kY kY'₁ hrange₀
  have hl₀_fac : l₀ ≫ kY = kY'₁ := PreAdicSpace.IsOpenImmersion.lift_fac kY kY'₁ hrange₀
  let α₀ := presentationLimitHomPairHom P P'₁ S S'₁ hP hP'₁ l₀
  -- 3. Shrink `Spa(A)` around `a₀` to a rational open `R(TA / sA)` mapping into `Set.range kY'₁`.
  let OA : Opens (presentationLimitPreAdicSpace P S.plus
      S.isRingOfIntegralElements.isPowerBounded_of_mem hP) :=
    ⟨kY.base ⁻¹' Set.range kY'₁.base, kY'₁.isOpenEmbedding.isOpen_range.preimage kY.base.hom.2⟩
  have ha₀O : a₀ ∈ OA := by
    obtain ⟨a'₁, ha'₁⟩ : (a'₀ : spa S'.plus) ∈ Set.range ιA'.base :=
      hιA'_range.symm ▸
        (ha'₀R : (a'₀ : spa S'.plus) ∈ (spaBasicOpen S'.plus TA' sA' : Set (spa S'.plus)))
    refine ⟨a'₁, ?_⟩
    have h1 := congrArg (fun m ↦ m.base c₀₀) hsq'
    have h2 : kY'₁.base a'₁ = kY'.base a'₀ := congrArg kY'.base ha'₁
    simpa [a'₀, hc₀₀, ha₀, h2] using h1
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
  have hsheafA₁ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair P S hP TA sA LA
    hdenA hTA hsheafA
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
  have hrange₁ : Set.range kY₁.base ⊆ Set.range kY'₁.base := by
    rintro _ ⟨z, rfl⟩
    have hz : (ιA.base z : spa S.plus) ∈ (spaBasicOpen S.plus TA sA : Set (spa S.plus)) :=
      hιA_range ▸ ⟨z, rfl⟩
    exact hRAO hz
  let l₁ := PreAdicSpace.IsOpenImmersion.lift kY'₁ kY₁ hrange₁
  have hl₁_fac : l₁ ≫ kY'₁ = kY₁ := PreAdicSpace.IsOpenImmersion.lift_fac kY'₁ kY₁ hrange₁
  let α₁ := presentationLimitHomPairHom P'₁ P₁ S'₁ S₁ hP'₁ hP₁ l₁
  have hl₁l₀ : l₁ ≫ l₀ = ιA := by
    rw [← cancel_mono kY, Category.assoc, hl₀_fac, hl₁_fac]
  have hα₁α₀ : α₁.comp α₀ = P.toCompletionLocHom S hP TA sA LA hdenA := by
    have h := congrArg (presentationLimitHomPairHom P P₁ S S₁ hP hP₁) hl₁l₀
    rwa [presentationLimitHomPairHom_comp P P'₁ P₁ S S'₁ S₁ hP hP'₁ hP₁,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P P₁ S S₁ hP hP₁
        hsheafA₁] at h
  have hα₁_tft : α₁.IsTopologicallyFiniteType :=
    Pair.Hom.IsTopologicallyFiniteType.of_comp (hα₁α₀ ▸
      P.isTopologicallyFiniteType_toCompletionLocHom S hP TA sA LA hdenA
        (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTA))
  have hStdA₁ : IsHuberStandard (UniformSpace.Completion LA) := by
    have := hStdA'₁
    exact .of_isTopologicallyFiniteType hα₁_tft.isTopologicallyFiniteType_toRingHom
  refine ⟨hStdA₁, ?_⟩
  -- 4. Shrink `Spa(C₁)` around `c₁₀` to `R(TC₁ / sC₁)` mapping into `Set.range kY₁`.
  let OC₁ : Opens (presentationLimitPreAdicSpace PC₁ U₁.plus
      U₁.isRingOfIntegralElements.isPowerBounded_of_mem hPC₁) :=
    ⟨(kX₁ ≫ f.hom).base ⁻¹' Set.range kY₁.base,
      kY₁.isOpenEmbedding.isOpen_range.preimage (kX₁ ≫ f.hom).base.hom.2⟩
  have hc₁₀O : c₁₀ ∈ OC₁ := by
    obtain ⟨a₁, ha₁⟩ : (a₀ : spa S.plus) ∈ Set.range ιA.base :=
      hιA_range.symm ▸ (ha₀R : (a₀ : spa S.plus) ∈ (spaBasicOpen S.plus TA sA : Set (spa S.plus)))
    refine ⟨a₁, ?_⟩
    simpa [kY₁, hc₁₀_x, ← ha₀] using congrArg kY.base ha₁
  obtain ⟨RC₁, hRC₁, hc₁₀R, hRC₁O⟩ :=
    Opens.isBasis_iff_nbhd.mp (isBasis_spaRationalOpens U₁.plus) hc₁₀O
  obtain ⟨TC₁, sC₁, hTC₁, rfl⟩ := mem_spaRationalOpens_iff_exists_spaBasicOpen.mp hRC₁
  let LC₁ := Localization.Away sC₁
  have hdenC₁ := PC₁.hasDenominatorPower_of_isOpen_span TC₁ sC₁ LC₁ hTC₁
  let _ := PC₁.locUniformSpace TC₁ sC₁ LC₁ hdenC₁
  have _ := PC₁.isUniformAddGroup_locUniformSpace TC₁ sC₁ LC₁ hdenC₁
  have _ := PC₁.isTopologicalRing_locUniformSpace TC₁ sC₁ LC₁ hdenC₁
  have _ := PC₁.isHuberRing_completion_locTopology TC₁ sC₁ LC₁ hdenC₁
  let U₂ := PC₁.rationalLocalizationPair U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁
  let PC₂ := PC₁.completionLocalization TC₁ sC₁ LC₁ hdenC₁
  have hPC₂ : PC₂.ringOfDefinition ≤ U₂.plus := by
    rw [rationalLocalizationPair_plus]
    exact PC₁.completionLocalization_ringOfDefinition_le_completedPlusSubring U₁.plus hPC₁ TC₁ sC₁
      LC₁ hdenC₁
  have hsheafC₂ := isSheaf_presentationLimitPresheaf_rationalLocalizationPair PC₁ U₁ hPC₁ TC₁ sC₁
    LC₁ hdenC₁ hTC₁ hsheafC₁
  let ιC₁ := presentationLimitPreAdicSpacePairComap PC₁ PC₂ hPC₁ hPC₂ hsheafC₂
    (PC₁.toCompletionLocHom U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁)
  have hιC₁_imm : PreAdicSpace.IsOpenImmersion ιC₁ := by
    rw [show ιC₁ = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact isOpenImmersion_presentationLimitPreAdicSpaceComap_toCompletionLocHom PC₁ hPC₁ TC₁ sC₁
      LC₁ hdenC₁ hTC₁ hsheafC₂
  have hιC₁_range : Set.range ιC₁.base = (spaBasicOpen U₁.plus TC₁ sC₁ : Set (spa U₁.plus)) := by
    rw [show ιC₁ = _ from presentationLimitPreAdicSpacePairComap_def ..]
    exact range_presentationLimitPreAdicSpaceComap_toCompletionLocHom_base PC₁ hPC₁ TC₁ sC₁ LC₁
      hdenC₁ hsheafC₂
  let kX₂ := ιC₁ ≫ kX₁
  have hkX₂_imm : PreAdicSpace.IsOpenImmersion kX₂ := PreAdicSpace.IsOpenImmersion.comp ιC₁ kX₁
  obtain ⟨c₂, hc₂⟩ : (c₁₀ : spa U₁.plus) ∈ Set.range ιC₁.base :=
    hιC₁_range.symm ▸
      (hc₁₀R : (c₁₀ : spa U₁.plus) ∈ (spaBasicOpen U₁.plus TC₁ sC₁ : Set (spa U₁.plus)))
  have hrangeC₂ : Set.range (kX₂ ≫ f.hom).base ⊆ Set.range kY₁.base := by
    rintro _ ⟨z, rfl⟩
    have hz : (ιC₁.base z : spa U₁.plus) ∈ (spaBasicOpen U₁.plus TC₁ sC₁ : Set (spa U₁.plus)) :=
      hιC₁_range ▸ ⟨z, rfl⟩
    exact hRC₁O hz
  let q := PreAdicSpace.IsOpenImmersion.lift kY₁ (kX₂ ≫ f.hom) hrangeC₂
  have hq_fac : q ≫ kY₁ = kX₂ ≫ f.hom :=
    PreAdicSpace.IsOpenImmersion.lift_fac kY₁ (kX₂ ≫ f.hom) hrangeC₂
  let β := presentationLimitHomPairHom P₁ PC₂ S₁ U₂ hP₁ hPC₂ q
  have hql₁ : q ≫ l₁ =
      ιC₁ ≫ presentationLimitPreAdicSpacePairComap P'₁ PC₁ hP'₁ hPC₁ hsheafC₁ φ'₁ := by
    rw [← cancel_mono kY'₁, Category.assoc, hl₁_fac, hq_fac]
    dsimp only [kX₂]
    rw [Category.assoc, ← hsq'₁, Category.assoc]
  have hβα₁ : β.comp α₁ = (PC₁.toCompletionLocHom U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁).comp φ'₁ := by
    have h := congrArg (presentationLimitHomPairHom P'₁ PC₂ S'₁ U₂ hP'₁ hPC₂) hql₁
    rwa [presentationLimitHomPairHom_comp P'₁ P₁ PC₂ S'₁ S₁ U₂ hP'₁ hP₁ hPC₂,
      ← presentationLimitPreAdicSpacePairComap_comp P'₁ PC₁ PC₂ hP'₁ hPC₁ hPC₂ hsheafC₁ hsheafC₂,
      presentationLimitHomPairHom_presentationLimitPreAdicSpacePairComap P'₁ PC₂ S'₁ U₂ hP'₁ hPC₂
        hsheafC₂] at h
  have hψ'_tft :
      ((PC₁.toCompletionLocHom U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁).comp φ'₁).IsTopologicallyFiniteType :=
    PC₁.isTopologicallyFiniteType_toCompletionLocHom_comp U₁ hPC₁ TC₁ sC₁ LC₁ hdenC₁ φ'₁ hφ'₁
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTC₁)
  have hβ_tft : β.IsTopologicallyFiniteType :=
    Pair.Hom.IsTopologicallyFiniteType.of_comp (hβα₁ ▸ hψ'_tft)
  have hβ_fp : DiscreteTopology (UniformSpace.Completion LA) → β.toRingHom.FinitePresentation := by
    intro hDiscA₁
    have : IsHuberStandard (UniformSpace.Completion LA') := hStdA'₁
    rcases IsHuberStandard.discreteTopology_or_isNoetherianRing_of_isTopologicallyFiniteType
        hα₁_tft.isTopologicallyFiniteType_toRingHom with hDiscA'₁ | hNoethA₁
    · have : DiscreteTopology (UniformSpace.Completion LC₀) :=
        hφ'₁.isTopologicallyFiniteType_toRingHom.discreteTopology
      have hcomp_fp : (β.toRingHom.comp α₁.toRingHom).FinitePresentation := by
        rw [← Pair.Hom.toRingHom_comp, hβα₁, Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom]
        exact (PC₁.finitePresentation_toCompletionLoc_of_discreteTopology (TC₁ : Set _) sC₁ LC₁
          hdenC₁).comp (hfp'₁ hDiscA'₁)
      exact RingHom.FinitePresentation.of_comp_finiteType α₁.toRingHom hcomp_fp
        hα₁_tft.isTopologicallyFiniteType_toRingHom.finiteType
    · have : DiscreteTopology (UniformSpace.Completion LC₁) :=
        hβ_tft.isTopologicallyFiniteType_toRingHom.discreteTopology
      exact RingHom.FinitePresentation.of_finiteType.mp
        hβ_tft.isTopologicallyFiniteType_toRingHom.finiteType
  refine ⟨UniformSpace.Completion LC₁, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, U₂, PC₂, hPC₂, hsheafC₂, kX₂, hkX₂_imm,
    β, hβ_tft, hβ_fp, c₂, ?_, ?_⟩
  · simpa [kX₂, ← hc₁₀_x] using congrArg kX₁.base hc₂
  · rw [presentationLimitPreAdicSpacePairComap_presentationLimitHomPairHom P₁ PC₂ S₁ U₂ hP₁ hPC₂
      hsheafC₂]
    exact hq_fac

/-- **Composition of morphisms locally of finite presentation** (Huber 1996, §1.2): if
`f : X ⟶ Y` and `g : Y ⟶ Z` are locally of finite presentation, then `f ≫ g` is locally of finite
presentation. -/
theorem LocallyOfFinitePresentation.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : LocallyOfFinitePresentation f) (hg : LocallyOfFinitePresentation g) :
    LocallyOfFinitePresentation (f ≫ g) := by
  intro x
  obtain ⟨A, _, _, _, _, _, _, _, _, S, P, hP, -, B, _, _, _, _, _, _, _, T, P', hP', hsheafB,
    kY, hkY, kZ, hkZ, ψ, hψ, hψ_fp, b₀, hb₀, hsq_g⟩ :=
    hg.exists_openImmersion_chart (f.hom.base x)
  obtain ⟨TB, sB, hTB, -, -, C, _, _, _, _, _, _, _, U, PC, hPC, hsheafC, kX, hkX, β, hβ, hβ_fp,
    c₀, hc₀, hsq_f⟩ := hf.exists_openImmersion_over_rationalLocalization P' hP' hsheafB kY x hb₀
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
  let ψ₁ := (P'.toCompletionLocHom T hP' TB sB LB hdenB).comp ψ
  have hψ₁_tft : ψ₁.IsTopologicallyFiniteType :=
    P'.isTopologicallyFiniteType_toCompletionLocHom_comp T hP' TB sB LB hdenB ψ hψ
      (Submodule.isOpen_mono (Ideal.span_mono (Set.subset_insert _ _)) hTB)
  let χ := β.comp ψ₁
  have hχ_tft : χ.IsTopologicallyFiniteType := hβ.comp hψ₁_tft
  have hχ_fp : DiscreteTopology A → χ.toRingHom.FinitePresentation := fun hDiscA ↦ by
    have : DiscreteTopology B := hψ.isTopologicallyFiniteType_toRingHom.discreteTopology
    have : DiscreteTopology (UniformSpace.Completion LB) :=
      hψ₁_tft.isTopologicallyFiniteType_toRingHom.discreteTopology
    rw [Pair.Hom.toRingHom_comp, Pair.Hom.toRingHom_comp, toRingHom_toCompletionLocHom]
    exact (hβ_fp inferInstance).comp
      ((P'.finitePresentation_toCompletionLoc_of_discreteTopology (TB : Set B) sB LB hdenB).comp
        (hψ_fp hDiscA))
  refine exists_locallyOfFinitePresentation_chart_of_openImmersion_sq hP hPC hsheafC kX kZ χ
    hχ_tft hχ_fp hc₀ ?_
  rw [presentationLimitPreAdicSpacePairComap_comp P P₁' PC hP hP₁' hPC hsheafB₁ hsheafC,
    presentationLimitPreAdicSpacePairComap_comp P P' P₁' hP hP' hP₁' hsheafB hsheafB₁]
  simp only [Category.assoc]
  rw [hsq_g, reassoc_of% hsq_f, ObjectProperty.FullSubcategory.comp_hom]

/-- `LocallyOfFinitePresentation` is stable under composition in `AdicSpace`. -/
instance LocallyOfFinitePresentation.isStableUnderComposition :
    LocallyOfFinitePresentation.{u}.IsStableUnderComposition where
  comp_mem _ _ hf hg := hf.comp hg

end OpenImmersionCharts

end TauCeti.AdicSpace
