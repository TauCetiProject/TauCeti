/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Topology.Sheaves.Functors
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Defs
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Site-level congruence and additivity for pullback of sheaves of modules

Let `F : C ⥤ D` be a continuous functor between sites and `φ : S ⟶ F_* R` a morphism of sheaves of
rings. This file constructs the natural isomorphisms `SheafOfModules.pullbackCongr` and
`SheafOfModules.pullbackCongr₂` between pullback functors along equal ring-sheaf morphisms or
naturally isomorphic site functors, conjugate to Mathlib's `SheafOfModules.pushforwardCongr` and
`SheafOfModules.pushforwardCongr₂`, shows that `pushforward` between small sites in the same
universe is a right adjoint, and records that pullback along a morphism of ringed spaces is
additive.

## Main declarations

* `SheafOfModules.isRightAdjoint_pushforward`: pushforward of module sheaves between small sites
  in the same universe is a right adjoint;
* `SheafOfModules.pullbackCongr` and `SheafOfModules.pullbackCongr₂`: natural isomorphisms between
  pullback functors along equal ring-sheaf morphisms or naturally isomorphic site functors;
* `SheafOfModules.additive_pullback`: pullback of sheaves of modules along a morphism of ringed
  spaces is additive.
-/

public section

open CategoryTheory Limits TopologicalSpace

universe v v₁ v₂ u₁ u₂ u

noncomputable section

namespace SheafOfModules

section SiteCongr

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [Functor.IsContinuous F J K]
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}

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

end SiteCongr

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

end SheafOfModules

namespace TauCeti.SheafOfModules

variable {X Y : TopCat.{u}} {𝒪X : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {𝒪Y : Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}} {f : Y ⟶ X}
  (φ : ringCatSheaf 𝒪X ⟶
    ((Opens.map f).sheafPushforwardContinuous RingCat.{u} _ _).obj (ringCatSheaf 𝒪Y))
  [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]

/-- Pullback of sheaves of modules along a morphism of ringed spaces is additive. -/
instance _root_.SheafOfModules.additive_pullback :
    (_root_.SheafOfModules.pullback φ).Additive :=
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (_root_.SheafOfModules.pullback φ)
  Functor.additive_of_preservesBinaryBiproducts _

end TauCeti.SheafOfModules

end
