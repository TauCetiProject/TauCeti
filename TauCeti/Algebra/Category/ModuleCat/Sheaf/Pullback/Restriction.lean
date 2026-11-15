/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Topology.Sheaves.Module
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.LocalIsomorphism
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction
public import TauCeti.CategoryTheory.Adjunction.Mates

/-!
# Pullback coherence and open-subspace restriction of sheaves of modules

Let `F : C ⥤ D` be a continuous functor between sites and `φ : S ⟶ F_* R` a morphism of sheaves of
rings. Mathlib defines the unit comparisons `SheafOfModules.unitToPushforwardObjUnit φ` and
`SheafOfModules.pullbackObjUnitToUnit φ` and proves that the latter is invertible when `F` is
final. This file supplies the identity, composition, and congruence coherences for these unit
comparisons, packages `pullbackObjUnitToUnit φ` as an isomorphism
`SheafOfModules.pullbackObjUnitIso` when `F` is final, and constructs the natural isomorphisms
`SheafOfModules.pullbackCongr` and `SheafOfModules.pullbackCongr₂` conjugate to
`SheafOfModules.pushforwardCongr` and `SheafOfModules.pushforwardCongr₂`.

For a topological space `X`, a sheaf of rings `R` on `X`, and an open subset `U : Opens X`,
restriction of sheaves of `R`-modules to the open subspace `U` is defined as pushforward along the
open-image functor `U.isOpenEmbedding_topCatInclusion.functor`
(`TopologicalSpace.Opens.sheafOfModulesRestrict`). Via the site adjunction
`U.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction`, restriction is left adjoint to direct
image along `U.topCatInclusion : TopCat.of U ⟶ X`, hence naturally isomorphic to pullback along the
canonical ring map `U.sheafInclusionHom RingCat R`. At the same time, restriction at universe `u`
has its own left adjoint (extension by zero), so both `U.sheafOfModulesRestrict R` and pullback
along `U.sheafInclusionHom RingCat R` preserve all limits as well as all colimits. Under Mathlib's
slice equivalence `U.sheafOfModulesEquivOver R`, open-subspace restriction agrees with slice
restriction `SheafOfModules.overFunctor R U` and preserves free module sheaves. Consequently,
isomorphisms, monomorphisms, epimorphisms, and vanishing of module sheaves on `X` can be tested
after restriction or pullback to the members of an open cover.

For a continuous map `f : X ⟶ Y` and a morphism of sheaves of rings `φ : S ⟶ f_* R`, restricting a
sheaf of rings to opens `V ⊆ Y` and `U ⊆ f⁻¹(V)` produces a restricted ring-sheaf morphism
`TopologicalSpace.Opens.sheafHomResLE φ V U e` along `TopologicalSpace.Opens.resLE f V U e : U ⟶ V`.
Module pullback commutes with open-subspace restriction (`SheafOfModules.restrictPullbackIso`),
yielding the slice-site pullback functor `SheafOfModules.pullbackOver φ V` together with its unit
and object comparisons `SheafOfModules.pullbackOverUnitIso` and
`SheafOfModules.pullbackOverObjIso`.

## Main declarations

* `SheafOfModules.pullbackObjUnitIso`: the isomorphism `(pullback φ).obj (unit S) ≅ unit R` when the
  underlying continuous functor `F` is final, with identity and composition coherences
  `pullbackObjUnitIso_id`, `pullbackObjUnitIso_comp`, and `pullbackObjUnitIso_inv_comp`;
* `SheafOfModules.pullbackCongr` and `SheafOfModules.pullbackCongr₂`: natural isomorphisms between
  pullback functors along equal ring-sheaf morphisms or naturally isomorphic site functors;
* `SheafOfModules.isRightAdjoint_pushforward`: pushforward of module sheaves between small sites in
  the same universe is a right adjoint;
* `TopologicalSpace.Opens.topCatInclusion`, `TopologicalSpace.Opens.sheafInclusionHom`, and
  `TopologicalSpace.Opens.sheafHomResLE`: the inclusion `TopCat.of U ⟶ X`, the canonical sheaf
  morphism `F ⟶ (U.topCatInclusion)_* (F|_U)`, and the restriction of `φ : S ⟶ f_* R` to opens
  `V ⊆ Y` and `U ⊆ f⁻¹(V)`;
* `TopologicalSpace.Opens.sheafOfModulesRestrict`,
  `TopologicalSpace.Opens.sheafOfModulesRestrictAdj`, and
  `TopologicalSpace.Opens.sheafOfModulesRestrictIsoPullback`: restriction of module sheaves to
  an open subspace, its adjunction with direct image, and its identification with pullback;
* `SheafOfModules.restrictPullbackIso` and `SheafOfModules.pullbackOver`: compatibility of module
  pullback with open-subspace restriction, and the induced pullback between slice sites;
* `SheafOfModules.isIso_iff_pullback_of_isOpenCover`,
  `SheafOfModules.mono_iff_pullback_of_isOpenCover`,
  `SheafOfModules.epi_iff_pullback_of_isOpenCover`, and
  `SheafOfModules.isZero_iff_pullback_of_isOpenCover`: open-cover locality of isomorphisms,
  monomorphisms, epimorphisms, and zero objects for module sheaves on ringed spaces.

## References

* [The Stacks Project, Tag 008F](https://stacks.math.columbia.edu/tag/008F)
* [The Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace Topology

universe v v₁ v₂ v₃ u₁ u₂ u₃ u

noncomputable section

namespace SheafOfModules

section SiteCoherence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F : C ⥤ D} {G : D ⥤ E}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G K L]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {T : Sheaf L RingCat.{u}}

/-- Along the identity morphism of ring sheaves, `unitToPushforwardObjUnit` is the inverse of the
identity comparison `pushforwardId`. -/
@[reassoc]
theorem unitToPushforwardObjUnit_id (S : Sheaf J RingCat.{u}) :
    unitToPushforwardObjUnit (F := 𝟭 C) (𝟙 S) ≫ (pushforwardId S).hom.app (unit S) =
      𝟙 (unit S) := by
  ext U
  rfl

/-- Composing `unitToPushforwardObjUnit` along `φ` and `ψ` through `pushforwardComp` gives
`unitToPushforwardObjUnit` for the composite morphism of ring sheaves. -/
@[reassoc]
theorem unitToPushforwardObjUnit_comp
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T) :
    haveI : Functor.IsContinuous (F ⋙ G) J L := Functor.isContinuous_comp F G J K L
    unitToPushforwardObjUnit φ ≫ (pushforward φ).map (unitToPushforwardObjUnit ψ) ≫
        (pushforwardComp φ ψ).hom.app (unit T) =
      unitToPushforwardObjUnit (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) := by
  ext U
  rfl

/-- Along the identity morphism of ring sheaves, `pullbackObjUnitToUnit` is the component of
`pullbackId` at the unit module sheaf. -/
theorem pullbackObjUnitToUnit_id (S : Sheaf J RingCat.{u}) :
    pullbackObjUnitToUnit (F := 𝟭 C) (𝟙 S) = (pullbackId S).hom.app (unit S) := by
  apply ((pullbackPushforwardAdjunction.{u} (F := 𝟭 C) (𝟙 S)).homEquiv _ _).injective
  refine (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit (F := 𝟭 C) (𝟙 S)).trans ?_
  rw [Adjunction.homEquiv_unit, ← unit_conjugateEquiv Adjunction.id, conjugateEquiv_pullbackId_hom]
  ext U
  rfl

/-- Along a composite of morphisms of ring sheaves, `pullbackObjUnitToUnit` factors through
`pullbackComp`. -/
@[reassoc]
theorem pullbackObjUnitToUnit_comp
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T)
    [(pushforward.{u} φ).IsRightAdjoint] [(pushforward.{u} ψ).IsRightAdjoint]
    [(F ⋙ G).IsContinuous J L] :
    (pullbackComp φ ψ).inv.app (unit S) ≫ (pullback ψ).map (pullbackObjUnitToUnit φ) ≫
        pullbackObjUnitToUnit ψ =
      pullbackObjUnitToUnit (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ) := by
  apply ((pullbackPushforwardAdjunction.{u} (F := F ⋙ G)
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).homEquiv _ _).injective
  refine ((Adjunction.homEquiv_conjugateEquiv
      ((pullbackPushforwardAdjunction.{u} φ).comp (pullbackPushforwardAdjunction.{u} ψ))
      (pullbackPushforwardAdjunction.{u} (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ))
      (pullbackComp φ ψ).inv _).symm.trans ?_).trans
    (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit (F := F ⋙ G)
      (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).symm
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_homEquiv, Equiv.trans_apply,
    Adjunction.homEquiv_naturality_left,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
  refine (congrArg (· ≫ (pushforwardComp φ ψ).hom.app _)
    ((pullbackPushforwardAdjunction.{u} φ).homEquiv_naturality_right _ _)).trans ?_
  refine (congrArg (fun k ↦ (k ≫ _) ≫ _)
    (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ)).trans ?_
  exact (Category.assoc _ _ _).trans (unitToPushforwardObjUnit_comp φ ψ)

section UnitIso

variable (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
  [(pushforward.{u} φ).IsRightAdjoint] [F.Final]

/-- When the continuous functor `F` between sites is final, pullback along `φ` preserves the unit
sheaf of modules: `(pullback φ).obj (unit S) ≅ unit R`, with forward morphism
`pullbackObjUnitToUnit φ`. -/
def pullbackObjUnitIso : (pullback.{u} φ).obj (unit S) ≅ unit R :=
  @asIso _ _ _ _ (pullbackObjUnitToUnit φ) (instIsIsoPullbackObjUnitToUnitOfFinal φ)

/-- The forward morphism of `pullbackObjUnitIso` is `pullbackObjUnitToUnit`. -/
@[simp]
theorem pullbackObjUnitIso_hom : (pullbackObjUnitIso φ).hom = pullbackObjUnitToUnit φ :=
  (rfl)

/-- Under the pullback--pushforward adjunction, `pullbackObjUnitIso` corresponds to
`unitToPushforwardObjUnit`. -/
theorem pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitIso_hom :
    (pullbackPushforwardAdjunction.{u} φ).homEquiv _ _ (pullbackObjUnitIso φ).hom =
      unitToPushforwardObjUnit φ :=
  pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit φ

/-- Along the identity morphism of ring sheaves, `pullbackObjUnitIso` agrees with `pullbackId`. -/
theorem pullbackObjUnitIso_id (S : Sheaf J RingCat.{u}) :
    (pullbackObjUnitIso (F := 𝟭 C) (𝟙 S)).hom = (pullbackId S).hom.app (unit S) :=
  pullbackObjUnitToUnit_id S

/-- Along a composite of morphisms of ring sheaves over final functors, `pullbackObjUnitIso`
is compatible with `pullbackComp`. -/
@[reassoc]
theorem pullbackObjUnitIso_comp
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T)
    [(pushforward.{u} ψ).IsRightAdjoint] [G.Final] [(F ⋙ G).IsContinuous J L] :
    haveI : (F ⋙ G).Final := Functor.final_comp F G
    (pullbackComp φ ψ).inv.app (unit S) ≫ (pullback ψ).map (pullbackObjUnitIso φ).hom ≫
        (pullbackObjUnitIso ψ).hom =
      (pullbackObjUnitIso (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).hom :=
  pullbackObjUnitToUnit_comp φ ψ

/-- Inverse form of `pullbackObjUnitIso_comp`: the inverse unit comparison for a composite factors
into the inverse unit comparisons of the two steps followed by `pullbackComp`. -/
@[reassoc]
theorem pullbackObjUnitIso_inv_comp
    (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{u} K L).obj T)
    [(pushforward.{u} ψ).IsRightAdjoint] [G.Final] [(F ⋙ G).IsContinuous J L] :
    haveI : (F ⋙ G).Final := Functor.final_comp F G
    (pullbackObjUnitIso ψ).inv ≫ (pullback ψ).map (pullbackObjUnitIso φ).inv ≫
        (pullbackComp φ ψ).hom.app (unit S) =
      (pullbackObjUnitIso (F := F ⋙ G)
        (φ ≫ (F.sheafPushforwardContinuous RingCat.{u} J K).map ψ)).inv := by
  have : (F ⋙ G).Final := Functor.final_comp F G
  refine (Iso.inv_ext ?_).symm
  rw [← pullbackObjUnitIso_comp φ ψ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_map_assoc, Iso.inv_hom_id_app]

end UnitIso

section PullbackCongr

/-- Pullback functors along equal morphisms of sheaves of rings are naturally isomorphic, as the
conjugate of `pushforwardCongr`. -/
def pullbackCongr {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ)
    [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{v} ψ).IsRightAdjoint] :
    pullback.{v} φ ≅ pullback.{v} ψ :=
  ((conjugateIsoEquiv (pullbackPushforwardAdjunction.{v} φ)
    (pullbackPushforwardAdjunction.{v} ψ)).symm (pushforwardCongr.{v} e)).symm

/-- The inverse of `pullbackCongr` is conjugate to `pushforwardCongr`. -/
@[simp]
theorem conjugateEquiv_pullbackCongr_inv
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ)
    [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{v} ψ).IsRightAdjoint] :
    conjugateEquiv (pullbackPushforwardAdjunction.{v} φ)
      (pullbackPushforwardAdjunction.{v} ψ) (pullbackCongr.{v} e).inv =
      (pushforwardCongr.{v} e).hom :=
  (conjugateEquiv _ _).apply_symm_apply _

/-- `pullbackCongr` on a reflexivity proof is the identity natural isomorphism. -/
@[simp]
theorem pullbackCongr_refl (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    [(pushforward.{v} φ).IsRightAdjoint] :
    pullbackCongr.{v} (rfl : φ = φ) = Iso.refl (pullback.{v} φ) := by
  have h : pushforwardCongr.{v} (rfl : φ = φ) = Iso.refl (pushforward.{v} φ) := by
    ext M U
    rfl
  have hsymm : (conjugateIsoEquiv (pullbackPushforwardAdjunction.{v} φ)
      (pullbackPushforwardAdjunction.{v} φ)).symm (Iso.refl _) = Iso.refl _ :=
    (conjugateIsoEquiv _ _).symm_apply_eq.mpr (Iso.ext (by simp))
  rw [pullbackCongr, h, hsymm, Iso.refl_symm]

/-- Symmetry of `pullbackCongr` reverses the equality proof. -/
@[simp]
theorem pullbackCongr_symm {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    (e : φ = ψ) [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{v} ψ).IsRightAdjoint] :
    (pullbackCongr.{v} e).symm = pullbackCongr.{v} e.symm := by
  subst e
  simp

/-- `pullbackCongr` commutes with `pullbackObjUnitToUnit`. -/
@[reassoc]
theorem pullbackCongr_hom_app_pullbackObjUnitToUnit
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ)
    [(pushforward.{u} φ).IsRightAdjoint] [(pushforward.{u} ψ).IsRightAdjoint] :
    (pullbackCongr.{u} e).hom.app (unit S) ≫ pullbackObjUnitToUnit ψ =
      pullbackObjUnitToUnit φ := by
  subst e
  simp

/-- Pullback functors along naturally isomorphic continuous functors and compatible ring-sheaf
morphisms are naturally isomorphic, as the conjugate of `pushforwardCongr₂`. -/
def pullbackCongr₂ {F' : C ⥤ D} [Functor.IsContinuous F' J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {ψ : S ⟶ (F'.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    (e : F' ≅ F)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app R = ψ)
    [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{v} ψ).IsRightAdjoint] :
    pullback.{v} φ ≅ pullback.{v} ψ :=
  ((conjugateIsoEquiv (pullbackPushforwardAdjunction.{v} φ)
    (pullbackPushforwardAdjunction.{v} ψ)).symm (pushforwardCongr₂.{v} φ e he)).symm

/-- The inverse of `pullbackCongr₂` is conjugate to `pushforwardCongr₂`. -/
@[simp]
theorem conjugateEquiv_pullbackCongr₂_inv {F' : C ⥤ D} [Functor.IsContinuous F' J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {ψ : S ⟶ (F'.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    (e : F' ≅ F)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app R = ψ)
    [(pushforward.{v} φ).IsRightAdjoint] [(pushforward.{v} ψ).IsRightAdjoint] :
    conjugateEquiv (pullbackPushforwardAdjunction.{v} φ)
      (pullbackPushforwardAdjunction.{v} ψ) (pullbackCongr₂.{v} φ e he).inv =
      (pushforwardCongr₂.{v} φ e he).hom :=
  (conjugateEquiv _ _).apply_symm_apply _

end PullbackCongr

/-- Between small sites in the same universe, pushforward of module sheaves along any continuous
functor and ring-sheaf morphism is a right adjoint. This is a theorem rather than a global instance
so that explicit `[IsRightAdjoint]` hypotheses on general site-level lemmas do not become redundant
instance binders. -/
theorem isRightAdjoint_pushforward {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    [Functor.IsContinuous F J K] {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
    [HasWeakSheafify K AddCommGrpCat.{u}] [K.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R) :
    (pushforward.{u} φ).IsRightAdjoint :=
  have := PresheafOfModules.instIsRightAdjointPushforward (F := F) φ.hom
  inferInstance

end SiteCoherence

end SheafOfModules

namespace TopologicalSpace.Opens

section SheafRestriction

/-- `Opens.map g` is continuous for the open-cover topologies when the domain is written as
`TopCat.of α` and the topology on the domain is written on the unbundled type `α`. -/
instance isContinuous_map_topCatOf_left {α : Type u} [TopologicalSpace α] {Y : TopCat.{u}}
    (g : TopCat.of α ⟶ Y) :
    (Opens.map g).IsContinuous (Opens.grothendieckTopology Y) (Opens.grothendieckTopology α) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map g) (coverPreserving_opens_map g)

/-- `Opens.map g` is continuous for the open-cover topologies when the codomain is written as
`TopCat.of β` and the topology on the codomain is written on the unbundled type `β`. -/
instance isContinuous_map_topCatOf_right {X : TopCat.{u}} {β : Type u} [TopologicalSpace β]
    (g : X ⟶ TopCat.of β) :
    (Opens.map g).IsContinuous (Opens.grothendieckTopology β) (Opens.grothendieckTopology X) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map g) (coverPreserving_opens_map g)

/-- `Opens.map g` is continuous for the open-cover topologies when both endpoints are written via
`TopCat.of` and their Grothendieck topologies are written on the unbundled types. -/
instance isContinuous_map_topCatOf_both {α β : Type u} [TopologicalSpace α] [TopologicalSpace β]
    (g : TopCat.of α ⟶ TopCat.of β) :
    (Opens.map g).IsContinuous (Opens.grothendieckTopology β) (Opens.grothendieckTopology α) :=
  Functor.isContinuous_of_coverPreserving
    (compatiblePreserving_opens_map g) (coverPreserving_opens_map g)

variable {X Y : TopCat.{u}}

/-- The inclusion map `U ⟶ X` from an open subset to the whole space as a morphism in `TopCat`
with domain `TopCat.of U`, so that its underlying topological space is reducibly `↥U` (matching
`Opens.sheafRestrict` and `Opens.grothendieckTopology U`). Its body is exposed so that
`U.isOpenEmbedding_topCatInclusion` reduces in downstream sectionwise formulas. -/
@[expose]
def topCatInclusion (U : Opens X) : TopCat.of U ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The underlying function of `Opens.topCatInclusion` is `Subtype.val`. -/
@[simp]
theorem coe_topCatInclusion (U : Opens X) : (U.topCatInclusion : U → X) = Subtype.val :=
  (rfl)

/-- `Opens.topCatInclusion` is an open embedding. -/
theorem isOpenEmbedding_topCatInclusion (U : Opens X) : IsOpenEmbedding U.topCatInclusion :=
  U.2.isOpenEmbedding_subtypeVal

/-- For an open subset `U` of `X` and a sheaf `F` on `X`, the canonical morphism
`F ⟶ (U.topCatInclusion)_* (F|_U)` induced by the counit
`(U.topCatInclusion) '' ((U.topCatInclusion)⁻¹ W) ≤ W` of
`U.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction`. -/
def sheafInclusionHom (U : Opens X) (A : Type*) [Category* A] (F : X.Sheaf A) :
    F ⟶ ((Opens.map U.topCatInclusion).sheafPushforwardContinuous A
      (Opens.grothendieckTopology X) (Opens.grothendieckTopology U)).obj
        (U.sheafRestrict.obj F) where
  hom :=
    Functor.whiskerRight
      (NatTrans.op U.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction.counit) F.obj

/-- On sections over `W`, `sheafInclusionHom` restricts along `W ⊓ U ≤ W`. -/
@[simp]
theorem sheafInclusionHom_hom_app (U : Opens X) (A : Type*) [Category* A]
    (F : X.Sheaf A) (W : (Opens X)ᵒᵖ) :
    (U.sheafInclusionHom A F).hom.app W =
      F.obj.map (U.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction.counit.app W.unop).op :=
  (rfl)

/-- The continuous map `U ⟶ V` between open subspaces induced by `f : X ⟶ Y` when
`U ≤ (Opens.map f).obj V`. Its body is exposed so that `(Opens.map (Opens.resLE f V U e)).obj`
reduces on open subsets. -/
@[expose]
def resLE (f : X ⟶ Y) (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    TopCat.of U ⟶ TopCat.of V :=
  TopCat.ofHom ⟨fun x ↦ ⟨f x.1, e x.2⟩, (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩

/-- Underlying point value of `Opens.resLE`. -/
@[simp]
theorem coe_resLE_apply (f : X ⟶ Y) (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V)
    (x : U) : (Opens.resLE f V U e x).1 = f x.1 :=
  (rfl)

/-- `Opens.resLE` commutes with the open inclusions into `X` and `Y`. -/
@[reassoc (attr := simp)]
theorem resLE_comp_topCatInclusion (f : X ⟶ Y) (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    Opens.resLE f V U e ≫ V.topCatInclusion = U.topCatInclusion ≫ f := by
  ext x
  rfl

/-- For an open `W` of `V` and `e : U ≤ (Opens.map f).obj V`, the image in `X` of the preimage of
`W` under `Opens.resLE f V U e` is contained in the preimage under `f` of the image of `W` in
`Y`. -/
theorem functor_map_resLE_le (f : X ⟶ Y) (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) (W : Opens V) :
    U.isOpenEmbedding_topCatInclusion.functor.obj ((Opens.map (Opens.resLE f V U e)).obj W) ≤
      (Opens.map f).obj (V.isOpenEmbedding_topCatInclusion.functor.obj W) := by
  rintro _ ⟨u, hu, rfl⟩
  exact ⟨⟨f u.1, e u.2⟩, hu, rfl⟩

/-- Restriction of a sheaf morphism `φ : S ⟶ f_* R` to open subspaces `V ⊆ Y` and `U ⊆ f⁻¹(V)`
along `Opens.resLE f V U e : U ⟶ V`. -/
def sheafHomResLE {A : Type*} [Category* A] {f : X ⟶ Y}
    {S : Y.Sheaf A} {R : X.Sheaf A}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    V.sheafRestrict.obj S ⟶ ((Opens.map (Opens.resLE f V U e)).sheafPushforwardContinuous A
      (Opens.grothendieckTopology V) (Opens.grothendieckTopology U)).obj
        (U.sheafRestrict.obj R) where
  hom :=
    { app W := φ.hom.app (op (V.isOpenEmbedding_topCatInclusion.functor.obj W.unop)) ≫
        R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e W.unop)).op
      naturality W₁ W₂ g := by
        let a := S.obj.map (V.isOpenEmbedding_topCatInclusion.functor.map g.unop).op
        let b₁ : S.obj.obj (op (V.isOpenEmbedding_topCatInclusion.functor.obj W₁.unop)) ⟶
            R.obj.obj (op ((Opens.map f).obj
              (V.isOpenEmbedding_topCatInclusion.functor.obj W₁.unop))) :=
          φ.hom.app (op (V.isOpenEmbedding_topCatInclusion.functor.obj W₁.unop))
        let b₂ : S.obj.obj (op (V.isOpenEmbedding_topCatInclusion.functor.obj W₂.unop)) ⟶
            R.obj.obj (op ((Opens.map f).obj
              (V.isOpenEmbedding_topCatInclusion.functor.obj W₂.unop))) :=
          φ.hom.app (op (V.isOpenEmbedding_topCatInclusion.functor.obj W₂.unop))
        let c₁ := R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e W₁.unop)).op
        let c₂ := R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e W₂.unop)).op
        let d := R.obj.map
          (U.isOpenEmbedding_topCatInclusion.functor.map
            ((Opens.map (Opens.resLE f V U e)).map g.unop)).op
        let e₀ := R.obj.map
          ((Opens.map f).map (V.isOpenEmbedding_topCatInclusion.functor.map g.unop)).op
        have hnat : a ≫ b₂ = b₁ ≫ e₀ :=
          φ.hom.naturality (V.isOpenEmbedding_topCatInclusion.functor.map g.unop).op
        have hR : e₀ ≫ c₂ = c₁ ≫ d := by
          rw [← R.obj.map_comp, ← R.obj.map_comp, ← op_comp, ← op_comp]
          exact congrArg (R.obj.map ∘ Quiver.Hom.op) (Subsingleton.elim _ _)
        change a ≫ (b₂ ≫ c₂) = (b₁ ≫ c₁) ≫ d
        exact (Category.assoc a b₂ c₂).symm.trans
          ((congrArg (· ≫ c₂) hnat).trans
            ((Category.assoc b₁ e₀ c₂).trans
              ((congrArg (b₁ ≫ ·) hR).trans (Category.assoc b₁ c₁ d).symm))) }

/-- Component of `Opens.sheafHomResLE` on an open `W` of `V`. -/
@[simp]
theorem sheafHomResLE_hom_app {A : Type*} [Category* A] {f : X ⟶ Y}
    {S : Y.Sheaf A} {R : X.Sheaf A}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) (W : (Opens V)ᵒᵖ) :
    (Opens.sheafHomResLE φ V U e).hom.app W =
      φ.hom.app (op (V.isOpenEmbedding_topCatInclusion.functor.obj W.unop)) ≫
        R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e W.unop)).op :=
  (rfl)

/-- Natural isomorphism between composed open-preimage functors witnessing the commutative square
`resLE_comp_topCatInclusion`. -/
def mapCompResLEIso (f : X ⟶ Y) (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    Opens.map f ⋙ Opens.map U.topCatInclusion ≅
      Opens.map V.topCatInclusion ⋙ Opens.map (Opens.resLE f V U e) :=
  Opens.mapIso (U.topCatInclusion ≫ f) (Opens.resLE f V U e ≫ V.topCatInclusion)
    (Opens.resLE_comp_topCatInclusion f V U e).symm

/-- Compatibility of `sheafHomResLE` with `sheafInclusionHom`: restricting `S` to `V` and applying
`sheafHomResLE` agrees with applying `φ` and restricting `R` to `U` along the commutative square
`resLE_comp_topCatInclusion`. -/
theorem sheafInclusionHom_comp_map_sheafHomResLE {A : Type*} [Category* A] {f : X ⟶ Y}
    {S : Y.Sheaf A} {R : X.Sheaf A}
    (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous A
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    letI : (Opens.map f ⋙ Opens.map U.topCatInclusion).IsContinuous
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U) :=
      Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
    letI : (Opens.map V.topCatInclusion ⋙ Opens.map (Opens.resLE f V U e)).IsContinuous
        (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U) :=
      Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology V) _
    (V.sheafInclusionHom A S ≫
          ((Opens.map V.topCatInclusion).sheafPushforwardContinuous A
            (Opens.grothendieckTopology Y) (Opens.grothendieckTopology V)).map
              (Opens.sheafHomResLE φ V U e) :
        S ⟶ ((Opens.map V.topCatInclusion ⋙
            Opens.map (Opens.resLE f V U e)).sheafPushforwardContinuous
          A (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U)).obj
            (U.sheafRestrict.obj R)) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (Opens.mapCompResLEIso f V U e).hom A
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U)).app
            (U.sheafRestrict.obj R) =
      (φ ≫ ((Opens.map f).sheafPushforwardContinuous A
          (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).map
            (U.sheafInclusionHom A R) :
        S ⟶ ((Opens.map f ⋙ Opens.map U.topCatInclusion).sheafPushforwardContinuous
          A (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U)).obj
            (U.sheafRestrict.obj R)) := by
  have : (Opens.map f ⋙ Opens.map U.topCatInclusion).IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
  have : (Opens.map V.topCatInclusion ⋙ Opens.map (Opens.resLE f V U e)).IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology V) _
  refine Sheaf.hom_ext (NatTrans.ext (funext fun Z ↦ ?_))
  let τ := (Opens.mapCompResLEIso f V U e).hom
  let a := S.obj.map (V.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction.counit.app Z.unop).op
  let b₁ : S.obj.obj Z ⟶ R.obj.obj (op ((Opens.map f).obj Z.unop)) := φ.hom.app Z
  let b₂ : S.obj.obj (op (V.isOpenEmbedding_topCatInclusion.functor.obj
        ((Opens.map V.topCatInclusion).obj Z.unop))) ⟶
      R.obj.obj (op ((Opens.map f).obj (V.isOpenEmbedding_topCatInclusion.functor.obj
        ((Opens.map V.topCatInclusion).obj Z.unop)))) :=
    φ.hom.app (op (V.isOpenEmbedding_topCatInclusion.functor.obj
      ((Opens.map V.topCatInclusion).obj Z.unop)))
  let c := R.obj.map (homOfLE (Opens.functor_map_resLE_le f V U e
    ((Opens.map V.topCatInclusion).obj Z.unop))).op
  let d := R.obj.map (U.isOpenEmbedding_topCatInclusion.functor.map (τ.app Z.unop)).op
  let e₀ := R.obj.map ((Opens.map f).map
    (V.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction.counit.app Z.unop)).op
  let e₁ := R.obj.map (U.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction.counit.app
    ((Opens.map f).obj Z.unop)).op
  have hnat : a ≫ b₂ = b₁ ≫ e₀ :=
    φ.hom.naturality (V.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction.counit.app Z.unop).op
  have hR : (e₀ ≫ c) ≫ d = e₁ := by
    rw [← R.obj.map_comp, ← R.obj.map_comp, ← op_comp, ← op_comp]
    exact congrArg (R.obj.map ∘ Quiver.Hom.op) (Subsingleton.elim _ _)
  change (a ≫ (b₂ ≫ c)) ≫ d = b₁ ≫ e₁
  exact (congrArg (· ≫ d) ((Category.assoc a b₂ c).symm.trans
    ((congrArg (· ≫ c) hnat).trans (Category.assoc b₁ e₀ c)))).trans
      ((Category.assoc b₁ (e₀ ≫ c) d).trans (congrArg (b₁ ≫ ·) hR))

/-- For any continuous map `g`, the preimage functor `Opens.map g` is final, since every structured
arrow `W ⟶ (Opens.map g).obj V` maps to `W ⟶ (Opens.map g).obj ⊤`. -/
theorem final_map {X' Y' : TopCat} (g : X' ⟶ Y') :
    (Opens.map g).Final where
  out W := by
    let T : StructuredArrow W (Opens.map g) :=
      StructuredArrow.mk (homOfLE le_top : W ⟶ (Opens.map g).obj ⊤)
    have : Nonempty (StructuredArrow W (Opens.map g)) := ⟨T⟩
    exact zigzag_isConnected fun j₁ j₂ ↦
      Relation.ReflTransGen.tail
        (Relation.ReflTransGen.single
          (Or.inl ⟨(StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _) : j₁ ⟶ T)⟩))
        (Or.inr ⟨(StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _) : j₂ ⟶ T)⟩)

/-- Pulling back a covering family of opens along a continuous map `f : X ⟶ Y` gives a covering
family of opens of `X`. -/
theorem coversTop_map (f : X ⟶ Y) {ι : Type*} {V : ι → Opens Y}
    (hV : (Opens.grothendieckTopology Y).CoversTop V) :
    (Opens.grothendieckTopology X).CoversTop (fun i ↦ (Opens.map f).obj (V i)) := by
  rw [Opens.coversTop_iff] at hV ⊢
  rw [IsOpenCover, ← Function.comp_def, ← Opens.map_iSup, hV.iSup_eq_top, Opens.map_top]

end SheafRestriction

section ModuleRestriction

variable {X : TopCat.{u}} (U : Opens X) (R : X.Sheaf RingCat.{u})

/-- The open-image functor of `U.topCatInclusion` is continuous for the open-cover topologies. -/
instance isContinuous_isOpenEmbedding_topCatInclusion_functor :
    U.isOpenEmbedding_topCatInclusion.functor.IsContinuous
      (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) :=
  U.isOpenEmbedding_topCatInclusion.functor_isContinuous

/-- Restriction of sheaves of `R`-modules to an open subspace `U : Opens X`, defined as pushforward
along the open-image functor `U.isOpenEmbedding_topCatInclusion.functor : Opens U ⥤ Opens X`. -/
def sheafOfModulesRestrict :
    SheafOfModules.{v} R ⥤ SheafOfModules.{v} (U.sheafRestrict.obj R) :=
  SheafOfModules.pushforward.{v} (F := U.isOpenEmbedding_topCatInclusion.functor)
    (𝟙 (U.sheafRestrict.obj R))

/-- Restriction of module sheaves to an open subspace `U` is left adjoint to pushforward along
`U.topCatInclusion`. -/
def sheafOfModulesRestrictAdj :
    U.sheafOfModulesRestrict.{v} R ⊣
      SheafOfModules.pushforward.{v} (U.sheafInclusionHom RingCat.{u} R) := by
  refine
    SheafOfModules.pushforwardPushforwardAdj
      U.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction
      (𝟙 (U.sheafRestrict.obj R)) (U.sheafInclusionHom RingCat.{u} R) ?_ ?_
  · exact (Category.comp_id _).symm
  · refine NatTrans.ext (funext fun W ↦ ?_)
    let adj := U.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction
    change 𝟙 _ ≫
        (R.obj.map (adj.counit.app (U.isOpenEmbedding_topCatInclusion.functor.obj W.unop)).op ≫
          R.obj.map (U.isOpenEmbedding_topCatInclusion.functor.map (adj.unit.app W.unop)).op) =
      𝟙 (R.obj.obj (op (U.isOpenEmbedding_topCatInclusion.functor.obj W.unop)))
    rw [Category.id_comp, ← R.obj.map_comp, ← op_comp, adj.left_triangle_components W.unop]
    exact R.obj.map_id _

/-- Open-subspace restriction of module sheaves is a left adjoint (right adjoint: direct image). -/
instance isLeftAdjoint_sheafOfModulesRestrict :
    (U.sheafOfModulesRestrict.{v} R).IsLeftAdjoint :=
  (U.sheafOfModulesRestrictAdj.{v} R).isLeftAdjoint

/-- Direct image of module sheaves along `U.topCatInclusion` is a right adjoint at every module
universe `v` (left adjoint: `U.sheafOfModulesRestrict`). -/
instance isRightAdjoint_pushforward_sheafInclusionHom :
    (SheafOfModules.pushforward.{v} (U.sheafInclusionHom RingCat.{u} R)).IsRightAdjoint :=
  (U.sheafOfModulesRestrictAdj.{v} R).isRightAdjoint

/-- The counit of `sheafOfModulesRestrictAdj` is an isomorphism, since preimage followed by image
is the identity on opens of `U`. -/
instance isIso_sheafOfModulesRestrictAdj_counit :
    IsIso (U.sheafOfModulesRestrictAdj.{v} R).counit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have happ : ∀ W : (Opens U)ᵒᵖ,
      IsIso (((U.sheafOfModulesRestrictAdj.{v} R).counit.app M).val.app W) := fun W ↦ by
    let W' : Opens U :=
      (Opens.map U.topCatInclusion).obj (U.isOpenEmbedding_topCatInclusion.functor.obj W.unop)
    have heq : W' = W.unop :=
      Opens.map_functor_eq' U.topCatInclusion U.isOpenEmbedding_topCatInclusion W.unop
    have hhom : U.isOpenEmbedding_topCatInclusion.isOpenMap.adjunction.unit.app W.unop =
        eqToHom heq.symm :=
      Subsingleton.elim _ _
    have hmap : ⇑(((U.sheafOfModulesRestrictAdj.{v} R).counit.app M).val.app W) =
        ⇑(M.val.presheaf.map (eqToHom heq.symm).op) :=
      funext fun x ↦
        let x' : M.val.obj (op W') := x
        congrArg (fun k : W.unop ⟶ W' ↦ M.val.presheaf.map k.op x') hhom
    rw [ConcreteCategory.isIso_iff_bijective, hmap]
    exact (ConcreteCategory.isIso_iff_bijective _).mp
      (Functor.map_isIso M.val.presheaf (eqToHom heq.symm).op)
  have : IsIso ((SheafOfModules.forget _).map
      ((U.sheafOfModulesRestrictAdj.{v} R).counit.app M)) :=
    (PresheafOfModules.isoMk (fun W ↦ @asIso _ _ _ _ _ (happ W))
      (fun _ _ g ↦ ((U.sheafOfModulesRestrictAdj.{v} R).counit.app M).val.naturality g)).isIso_hom
  exact isIso_of_reflects_iso _ (SheafOfModules.forget _)

/-- Direct image of module sheaves along an open inclusion is full. -/
instance full_pushforward_sheafInclusionHom :
    (SheafOfModules.pushforward.{v} (U.sheafInclusionHom RingCat.{u} R)).Full :=
  (U.sheafOfModulesRestrictAdj.{v} R).fullyFaithfulROfIsIsoCounit.full

/-- Direct image of module sheaves along an open inclusion is faithful. -/
instance faithful_pushforward_sheafInclusionHom :
    (SheafOfModules.pushforward.{v} (U.sheafInclusionHom RingCat.{u} R)).Faithful :=
  (U.sheafOfModulesRestrictAdj.{v} R).fullyFaithfulROfIsIsoCounit.faithful

/-- At universe `u`, open-subspace restriction of module sheaves is also a right adjoint (its left
adjoint being extension by zero), so it preserves all limits. -/
instance isRightAdjoint_sheafOfModulesRestrict :
    (U.sheafOfModulesRestrict.{u} R).IsRightAdjoint :=
  SheafOfModules.isRightAdjoint_pushforward (F := U.isOpenEmbedding_topCatInclusion.functor)
    (𝟙 (U.sheafRestrict.obj R))

/-- Open-subspace restriction of module sheaves is an additive functor. -/
instance additive_sheafOfModulesRestrict :
    (U.sheafOfModulesRestrict.{v} R).Additive where
  map_add := rfl

/-- Open-subspace restriction of module sheaves is naturally isomorphic to pullback along
`U.sheafInclusionHom RingCat R`. -/
def sheafOfModulesRestrictIsoPullback :
    U.sheafOfModulesRestrict.{v} R ≅
      SheafOfModules.pullback.{v} (U.sheafInclusionHom RingCat.{u} R) :=
  (U.sheafOfModulesRestrictAdj.{v} R).leftAdjointUniq
    (SheafOfModules.pullbackPushforwardAdjunction.{v} (U.sheafInclusionHom RingCat.{u} R))

/-- Pullback of module sheaves along an open inclusion preserves all limits, since it is naturally
isomorphic to open-subspace restriction. -/
instance preservesLimits_pullback_sheafInclusionHom :
    PreservesLimits (SheafOfModules.pullback.{u} (U.sheafInclusionHom RingCat.{u} R)) :=
  preservesLimits_of_natIso (U.sheafOfModulesRestrictIsoPullback.{u} R)

/-- Restricting to the slice site over `U` and applying `U.sheafOfModulesEquivOver R` is naturally
isomorphic to open-subspace restriction `U.sheafOfModulesRestrict R`. -/
def overFunctorCompSheafOfModulesEquivOver :
    SheafOfModules.overFunctor.{v} R U ⋙ (U.sheafOfModulesEquivOver R).functor ≅
      U.sheafOfModulesRestrict.{v} R := by
  haveI : (U.overEquivalence.inverse ⋙ Over.forget U).IsContinuous
      (Opens.grothendieckTopology U) (Opens.grothendieckTopology X) :=
    Functor.isContinuous_comp _ _ _ ((Opens.grothendieckTopology X).over U) _
  refine SheafOfModules.pushforwardComp.{v} (U.overPullbackSheafEquivOver.app R).inv (𝟙 (R.over U))
    ≪≫ SheafOfModules.pushforwardCongr.{v} ?_
  ext : 2
  rfl

/-- Open-subspace restriction preserves the unit sheaf of modules. -/
def sheafOfModulesRestrictUnitIso :
    (U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit (U.sheafRestrict.obj R) :=
  haveI : (Opens.map U.topCatInclusion).Final := Opens.final_map U.topCatInclusion
  (U.sheafOfModulesRestrictIsoPullback.{u} R).app (SheafOfModules.unit R) ≪≫
    SheafOfModules.pullbackObjUnitIso (U.sheafInclusionHom RingCat.{u} R)

/-- Under `U.sheafOfModulesEquivOver R`, free module sheaves on the slice site over `U` correspond
to free module sheaves on the open subspace `U`. -/
def sheafOfModulesEquivOverFunctorObjFreeIso (I : Type u) :
    (U.sheafOfModulesEquivOver R).functor.obj (SheafOfModules.free I) ≅
      SheafOfModules.free I :=
  let F : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} (U.sheafRestrict.obj R) :=
    (U.sheafOfModulesEquivOver R).functor
  haveI : PreservesColimitsOfShape (Discrete I) F :=
    (U.sheafOfModulesEquivOver R).toAdjunction.leftAdjoint_preservesColimits
      |>.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso F I (U.sheafOfModulesEquivOverUnit R).symm).symm

/-- Open-subspace restriction sends the free module sheaf on `I` to the free module sheaf on `I`. -/
def sheafOfModulesRestrictFreeIso (I : Type u) :
    (U.sheafOfModulesRestrict.{u} R).obj (SheafOfModules.free I) ≅
      SheafOfModules.free I :=
  haveI : PreservesColimitsOfShape (Discrete I) (U.sheafOfModulesRestrict.{u} R) :=
    (U.sheafOfModulesRestrictAdj.{u} R).leftAdjoint_preservesColimits.preservesColimitsOfShape
  (SheafOfModules.mapFreeIso (U.sheafOfModulesRestrict.{u} R) I
    (U.sheafOfModulesRestrictUnitIso R).symm).symm

/-- A trivialization of `M.over U` by a free module sheaf induces a trivialization of the
open-subspace restriction `(U.sheafOfModulesRestrict R).obj M`. -/
def sheafOfModulesRestrictIsoFreeOfOverIsoFree (M : SheafOfModules.{u} R) {I : Type u}
    (e : M.over U ≅ SheafOfModules.free I) :
    (U.sheafOfModulesRestrict.{u} R).obj M ≅ SheafOfModules.free I :=
  ((U.overFunctorCompSheafOfModulesEquivOver R).app M).symm ≪≫
    (U.sheafOfModulesEquivOver R).functor.mapIso e ≪≫
    U.sheafOfModulesEquivOverFunctorObjFreeIso R I

/-- A trivialization of the open-subspace restriction `(U.sheafOfModulesRestrict R).obj M` by a free
module sheaf induces a trivialization of `M.over U`. -/
def overIsoFreeOfSheafOfModulesRestrictIsoFree (M : SheafOfModules.{u} R) {I : Type u}
    (e : (U.sheafOfModulesRestrict.{u} R).obj M ≅ SheafOfModules.free I) :
    M.over U ≅ SheafOfModules.free I :=
  (U.sheafOfModulesEquivOver R).fullyFaithfulFunctor.preimageIso
    ((U.overFunctorCompSheafOfModulesEquivOver R).app M ≪≫ e ≪≫
      (U.sheafOfModulesEquivOverFunctorObjFreeIso R I).symm)

end ModuleRestriction

end TopologicalSpace.Opens

namespace SheafOfModules

section RingedSpacePullback

variable {X Y : TopCat.{u}} {f : X ⟶ Y}
  {S : Y.Sheaf RingCat.{u}} {R : X.Sheaf RingCat.{u}}
  (φ : S ⟶ ((Opens.map f).sheafPushforwardContinuous RingCat.{u}
    (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj R)

/-- Pushforward of module sheaves along `Opens.sheafHomResLE φ V U e` is a right adjoint. -/
instance isRightAdjoint_pushforward_sheafHomResLE (V : Opens Y) (U : Opens X)
    (e : U ≤ (Opens.map f).obj V) :
    (pushforward.{u} (Opens.sheafHomResLE φ V U e)).IsRightAdjoint :=
  isRightAdjoint_pushforward (Opens.sheafHomResLE φ V U e)

/-- Module pullback along a ringed-space morphism `(f, φ)` commutes with restriction to open
subspaces `V ⊆ Y` and `U ⊆ f⁻¹(V)`. -/
def restrictPullbackIso [(pushforward.{u} φ).IsRightAdjoint]
    (V : Opens Y) (U : Opens X) (e : U ≤ (Opens.map f).obj V) :
    pullback.{u} φ ⋙ U.sheafOfModulesRestrict.{u} R ≅
      V.sheafOfModulesRestrict.{u} S ⋙ pullback.{u} (Opens.sheafHomResLE φ V U e) :=
  haveI : (Opens.map f ⋙ Opens.map U.topCatInclusion).IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology X) _
  haveI : (Opens.map V.topCatInclusion ⋙ Opens.map (Opens.resLE f V U e)).IsContinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology U) :=
    Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology V) _
  Functor.isoWhiskerLeft (pullback.{u} φ) (U.sheafOfModulesRestrictIsoPullback.{u} R) ≪≫
    pullbackComp.{u} φ (U.sheafInclusionHom RingCat.{u} R) ≪≫
    (pullbackCongr₂.{u} _ (Opens.mapCompResLEIso f V U e)
      (Opens.sheafInclusionHom_comp_map_sheafHomResLE φ V U e)).symm ≪≫
    (pullbackComp.{u} (V.sheafInclusionHom RingCat.{u} S)
      (Opens.sheafHomResLE φ V U e)).symm ≪≫
    Functor.isoWhiskerRight (V.sheafOfModulesRestrictIsoPullback.{u} S).symm
      (pullback.{u} (Opens.sheafHomResLE φ V U e))

/-- Pullback along `(f, φ)` read between slice sites over `V : Opens Y` and
`(Opens.map f).obj V : Opens X`, obtained by conjugating pullback along
`Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl` by Mathlib's `sheafOfModulesEquivOver`. -/
def pullbackOver (V : Opens Y) :
    SheafOfModules.{u} (S.over V) ⥤ SheafOfModules.{u} (R.over ((Opens.map f).obj V)) :=
  (V.sheafOfModulesEquivOver S).functor ⋙
    pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl) ⋙
    (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse

/-- Slice-site pullback `pullbackOver φ V` is a left adjoint, hence preserves all colimits. -/
instance isLeftAdjoint_pullbackOver (V : Opens Y) : (pullbackOver φ V).IsLeftAdjoint := by
  unfold pullbackOver
  infer_instance

/-- Slice-site pullback `pullbackOver φ V` preserves the unit sheaf of modules. -/
def pullbackOverUnitIso (V : Opens Y) :
    unit (R.over ((Opens.map f).obj V)) ≅ (pullbackOver φ V).obj (unit (S.over V)) :=
  haveI : (Opens.map (Opens.resLE f V ((Opens.map f).obj V) le_rfl)).Final :=
    Opens.final_map (Opens.resLE f V ((Opens.map f).obj V) le_rfl)
  (((Opens.map f).obj V).sheafOfModulesEquivOverInverseUnit R).symm ≪≫
    (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.mapIso
      ((pullbackObjUnitIso (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).symm ≪≫
        (pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).mapIso
          (V.sheafOfModulesEquivOverUnit S).symm)

/-- Slice-site pullback `pullbackOver φ V` computes the slice restriction of `(pullback φ).obj M`
to `(Opens.map f).obj V`. -/
def pullbackOverObjIso [(pushforward.{u} φ).IsRightAdjoint] (V : Opens Y)
    (M : SheafOfModules.{u} S) :
    (pullbackOver φ V).obj (M.over V) ≅ ((pullback.{u} φ).obj M).over ((Opens.map f).obj V) :=
  (((Opens.map f).obj V).sheafOfModulesEquivOver R).inverse.mapIso
      ((pullback.{u} (Opens.sheafHomResLE φ V ((Opens.map f).obj V) le_rfl)).mapIso
          ((V.overFunctorCompSheafOfModulesEquivOver S).app M) ≪≫
        ((restrictPullbackIso φ V ((Opens.map f).obj V) le_rfl).app M).symm ≪≫
        ((((Opens.map f).obj V).overFunctorCompSheafOfModulesEquivOver R).app
          ((pullback.{u} φ).obj M)).symm) ≪≫
    (((Opens.map f).obj V).sheafOfModulesEquivOver R).unitIso.symm.app
      (((pullback.{u} φ).obj M).over ((Opens.map f).obj V))

end RingedSpacePullback

section OpenCoverLocality

variable {X : TopCat.{u}} {R : X.Sheaf RingCat.{u}}
  {ι : Type*} {U : ι → Opens X}

/-- Open-subspace restrictions to the members of an open cover jointly reflect isomorphisms of
module sheaves. -/
theorem jointlyReflectIsomorphisms_sheafOfModulesRestrict (hU : IsOpenCover U) :
    JointlyReflectIsomorphisms (fun i ↦ (U i).sheafOfModulesRestrict.{v} R) where
  isIso φ h := by
    refine isIso_of_coversTop ((Opens.coversTop_iff X U).mpr hU) fun i ↦ ?_
    have hmap : IsIso (((U i).sheafOfModulesEquivOver R).functor.map (φ.over (U i))) :=
      (NatIso.isIso_map_iff ((U i).overFunctorCompSheafOfModulesEquivOver R) φ).mpr (h i)
    exact isIso_of_reflects_iso (φ.over (U i)) ((U i).sheafOfModulesEquivOver R).functor

/-- Pullbacks along the open inclusions of an open cover jointly reflect isomorphisms of module
sheaves. -/
theorem jointlyReflectIsomorphisms_pullback_sheafInclusionHom (hU : IsOpenCover U) :
    JointlyReflectIsomorphisms
      (fun i ↦ pullback.{v} ((U i).sheafInclusionHom RingCat.{u} R)) where
  isIso φ h := by
    have : ∀ i, IsIso (((U i).sheafOfModulesRestrict.{v} R).map φ) := fun i ↦
      (NatIso.isIso_map_iff ((U i).sheafOfModulesRestrictIsoPullback.{v} R) φ).mpr (h i)
    exact (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).isIso φ

/-- A morphism of module sheaves on `X` is an isomorphism if and only if its restrictions to the
members of an open cover are isomorphisms. -/
theorem isIso_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ i, IsIso (((U i).sheafOfModulesRestrict.{v} R).map φ) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦
    (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).isIso φ⟩

/-- A morphism of module sheaves on `X` is an isomorphism if and only if its pullbacks to the
members of an open cover are isomorphisms. -/
theorem isIso_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    IsIso φ ↔ ∀ i, IsIso ((pullback.{v} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  ⟨fun _ _ ↦ inferInstance, fun _ ↦
    (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).isIso φ⟩

/-- Monomorphisms of module sheaves on `X` can be checked after open-subspace restriction to an open
cover. -/
theorem mono_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Mono φ ↔ ∀ i, Mono (((U i).sheafOfModulesRestrict.{u} R).map φ) :=
  (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).jointlyReflectMonomorphisms.mono_iff φ

/-- Monomorphisms of module sheaves on `X` can be checked after pullback to an open cover. -/
theorem mono_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Mono φ ↔ ∀ i, Mono ((pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).jointlyReflectMonomorphisms.mono_iff φ

/-- Epimorphisms of module sheaves on `X` can be checked after open-subspace restriction to an open
cover. -/
theorem epi_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Epi φ ↔ ∀ i, Epi (((U i).sheafOfModulesRestrict.{u} R).map φ) :=
  haveI : ∀ i, ((U i).sheafOfModulesRestrict.{u} R).PreservesEpimorphisms :=
    fun _ ↦ Functor.preservesEpimorphisms_of_isLeftAdjoint _
  (jointlyReflectIsomorphisms_sheafOfModulesRestrict hU).jointlyReflectEpimorphisms.epi_iff φ

/-- Epimorphisms of module sheaves on `X` can be checked after pullback to an open cover. -/
theorem epi_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    {M N : SheafOfModules.{u} R} (φ : M ⟶ N) :
    Epi φ ↔ ∀ i, Epi ((pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).map φ) :=
  haveI : ∀ i, (pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).PreservesEpimorphisms :=
    fun _ ↦ Functor.preservesEpimorphisms_of_isLeftAdjoint _
  (jointlyReflectIsomorphisms_pullback_sheafInclusionHom hU).jointlyReflectEpimorphisms.epi_iff φ

/-- A module sheaf on `X` is zero if and only if its restrictions to the members of an open cover
are zero. -/
theorem isZero_iff_sheafOfModulesRestrict_of_isOpenCover (hU : IsOpenCover U)
    (M : SheafOfModules.{u} R) :
    IsZero M ↔ ∀ i, IsZero (((U i).sheafOfModulesRestrict.{u} R).obj M) := by
  refine ⟨fun hM i ↦ ((U i).sheafOfModulesRestrict.{u} R).map_isZero hM, fun h ↦ ?_⟩
  rw [IsZero.iff_id_eq_zero]
  have : IsIso (0 : M ⟶ M) := by
    rw [isIso_iff_sheafOfModulesRestrict_of_isOpenCover hU]
    intro i
    rw [Functor.map_zero, ← (h i).eq_of_src (𝟙 _) 0]
    infer_instance
  rw [← cancel_epi (0 : M ⟶ M), comp_zero, zero_comp]

/-- A module sheaf on `X` is zero if and only if its pullbacks to the members of an open cover are
zero. -/
theorem isZero_iff_pullback_of_isOpenCover (hU : IsOpenCover U)
    (M : SheafOfModules.{u} R) :
    IsZero M ↔ ∀ i, IsZero ((pullback.{u} ((U i).sheafInclusionHom RingCat.{u} R)).obj M) := by
  rw [isZero_iff_sheafOfModulesRestrict_of_isOpenCover hU]
  exact forall_congr' fun i ↦ (((U i).sheafOfModulesRestrictIsoPullback.{u} R).app M).isZero_iff

end OpenCoverLocality

end SheafOfModules

end
