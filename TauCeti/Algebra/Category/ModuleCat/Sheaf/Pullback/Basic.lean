/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import TauCeti.CategoryTheory.Adjunction.Mates

/-!
# Site-level coherence for pullback of sheaves of modules

Let `F : C ⥤ D` be a continuous functor between sites and `φ : S ⟶ F_* R` a morphism of sheaves of
rings. Mathlib defines the unit comparisons `SheafOfModules.unitToPushforwardObjUnit φ` and
`SheafOfModules.pullbackObjUnitToUnit φ` and proves that the latter is invertible when `F` is
final. This file supplies the identity, composition, and congruence coherences for these unit
comparisons, packages `pullbackObjUnitToUnit φ` as an isomorphism
`SheafOfModules.pullbackObjUnitIso` when `F` is final, constructs the natural isomorphisms
`SheafOfModules.pullbackCongr` and `SheafOfModules.pullbackCongr₂` conjugate to
`SheafOfModules.pushforwardCongr` and `SheafOfModules.pushforwardCongr₂`, and records that
pushforward between small sites in the same universe is a right adjoint.

## Main declarations

* `SheafOfModules.pullbackObjUnitIso`: the isomorphism `(pullback φ).obj (unit S) ≅ unit R` when the
  underlying continuous functor `F` is final, with identity and composition coherences
  `pullbackObjUnitIso_id`, `pullbackObjUnitIso_comp`, and `pullbackObjUnitIso_inv_comp`;
* `SheafOfModules.pullbackCongr` and `SheafOfModules.pullbackCongr₂`: natural isomorphisms between
  pullback functors along equal ring-sheaf morphisms or naturally isomorphic site functors;
* `SheafOfModules.isRightAdjoint_pushforward`: pushforward of module sheaves between small sites in
  the same universe is a right adjoint.
-/

public section

open CategoryTheory

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

end
