/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Basic
import TauCeti.CategoryTheory.Adjunction.Mates

/-!
# Site-level unit coherence for pullback of sheaves of modules

Let `F : C ⥤ D` be a continuous functor between sites and `φ : S ⟶ F_* R` a morphism of sheaves of
rings. Mathlib defines the unit comparisons `SheafOfModules.unitToPushforwardObjUnit φ` and
`SheafOfModules.pullbackObjUnitToUnit φ` and proves that the latter is invertible when `F` is
final. This file supplies the identity and composition coherences for these unit comparisons,
packages `pullbackObjUnitToUnit φ` as an isomorphism `SheafOfModules.pullbackObjUnitIso` when `F` is
final (together with its inverse composition law `pullbackObjUnitIso_inv_comp`), and records how
`pullbackObjUnitToUnit` interacts with `SheafOfModules.pullbackCongr` and
`SheafOfModules.pullbackCongr₂`.

## Main declarations

* `SheafOfModules.unitToPushforwardObjUnit_id` and
  `SheafOfModules.unitToPushforwardObjUnit_comp`: identity and composition coherences for
  `unitToPushforwardObjUnit`;
* `SheafOfModules.pullbackObjUnitToUnit_id` and `SheafOfModules.pullbackObjUnitToUnit_comp`:
  identity and composition coherences for `pullbackObjUnitToUnit`;
* `SheafOfModules.pullbackObjUnitIso`: the isomorphism `(pullback φ).obj (unit S) ≅ unit R` when the
  underlying continuous functor `F` is final, with `pullbackObjUnitIso_hom` and
  `pullbackObjUnitIso_inv_comp`;
* `SheafOfModules.pullbackCongr_hom_app_pullbackObjUnitToUnit` and
  `SheafOfModules.pullbackCongr₂_hom_app_pullbackObjUnitToUnit`: compatibility of
  `pullbackObjUnitToUnit` with `pullbackCongr` and `pullbackCongr₂`.
-/

public section

open CategoryTheory

universe v v₁ v₂ v₃ u₁ u₂ u₃ u

noncomputable section

namespace SheafOfModules

section SiteUnitCoherence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {L : GrothendieckTopology E}
  {F : C ⥤ D} {G : D ⥤ E}
  [Functor.IsContinuous F J K] [Functor.IsContinuous G K L]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}} {T : Sheaf L RingCat.{u}}

/-- Along the identity morphism of ring sheaves, `unitToPushforwardObjUnit` is the inverse of the
identity comparison `pushforwardId`. -/
@[reassoc (attr := simp)]
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
@[simp]
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

/-- Inverse composition law for `pullbackObjUnitIso`: the inverse unit comparison for a composite
factors into the inverse unit comparisons of the two steps followed by `pullbackComp`. -/
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
  rw [pullbackObjUnitIso_hom, ← pullbackObjUnitToUnit_comp φ ψ, ← pullbackObjUnitIso_hom φ,
    ← pullbackObjUnitIso_hom ψ]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_map_assoc, Iso.inv_hom_id_app]

end UnitIso

section PullbackCongr

/-- `pullbackCongr` commutes with `pullbackObjUnitToUnit`. -/
@[reassoc]
theorem pullbackCongr_hom_app_pullbackObjUnitToUnit
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R} (e : φ = ψ)
    [(pushforward.{u} φ).IsRightAdjoint] [(pushforward.{u} ψ).IsRightAdjoint] :
    (pullbackCongr.{u} e).hom.app (unit S) ≫ pullbackObjUnitToUnit ψ =
      pullbackObjUnitToUnit φ := by
  subst e
  simp

/-- `pullbackCongr₂` commutes with `pullbackObjUnitToUnit`. -/
@[reassoc]
theorem pullbackCongr₂_hom_app_pullbackObjUnitToUnit {F' : C ⥤ D} [Functor.IsContinuous F' J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    {ψ : S ⟶ (F'.sheafPushforwardContinuous RingCat.{u} J K).obj R}
    (e : F' ≅ F)
    (he : φ ≫ (Functor.sheafPushforwardContinuousNatTrans e.hom RingCat.{u} J K).app R = ψ)
    [(pushforward.{u} φ).IsRightAdjoint] [(pushforward.{u} ψ).IsRightAdjoint] :
    (pullbackCongr₂.{u} φ e he).hom.app (unit S) ≫ pullbackObjUnitToUnit ψ =
      pullbackObjUnitToUnit φ := by
  have hinv : (pullbackCongr₂.{u} φ e he).inv.app (unit S) ≫ pullbackObjUnitToUnit φ =
      pullbackObjUnitToUnit ψ := by
    apply ((pullbackPushforwardAdjunction.{u} ψ).homEquiv _ _).injective
    refine ((Adjunction.homEquiv_conjugateEquiv
        (pullbackPushforwardAdjunction.{u} φ)
        (pullbackPushforwardAdjunction.{u} ψ)
        (pullbackCongr₂.{u} φ e he).inv _).symm.trans ?_).trans
      (pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit ψ).symm
    rw [conjugateEquiv_pullbackCongr₂_inv,
      pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit]
    ext U
    change (((pushforwardCongr he).hom.app (unit R)).val.app U)
        (((pushforwardNatTrans φ e.hom).app (unit R)).val.app U
          ((unitToPushforwardObjUnit φ).val.app U (1 : S.obj.obj U))) =
      (unitToPushforwardObjUnit ψ).val.app U (1 : S.obj.obj U)
    rw [pushforwardCongr_hom_app_val_app, pushforwardNatTrans_app_val_app,
      unitToPushforwardObjUnit_val_app_apply, unitToPushforwardObjUnit_val_app_apply,
      map_one, map_one]
    exact (R.obj.map (e.hom.app U.unop).op).hom.map_one
  rw [← hinv, ← Category.assoc]
  simp

end PullbackCongr

end SiteUnitCoherence

end SheafOfModules

end
