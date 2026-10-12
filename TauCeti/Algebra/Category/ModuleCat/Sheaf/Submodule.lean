/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule

/-!
# Factoring a morphism through a submodule of a (pre)sheaf of modules

Mathlib's `PresheafOfModules.Submodule` and `SheafOfModules.Submodule` package a submodule of a
(pre)sheaf of modules together with the inclusion `N.ι` of the associated (pre)sheaf of modules.
This file supplies the missing universal property of that inclusion: a morphism whose sections all
land in `N` factors through `N`, uniquely because `N.ι` is a monomorphism.

## Main declarations

* `TauCeti.PresheafOfModules.liftToSubmodule` and `TauCeti.SheafOfModules.liftToSubmodule`, the
  factorization itself, with `liftToSubmodule_ι` recording that it does factor the given morphism;
* `TauCeti.SheafOfModules.isIso_liftToSubmodule`: the factorization is an isomorphism when the
  morphism is injective on sections with image exactly `N`;
* `TauCeti.SheafOfModules.Submodule.homOfLE`, the inclusion of one submodule of a sheaf of modules
  into a larger one;
* `SheafOfModules.Submodule.overIsoOfEq`, the identification over `V` of two submodules
  with the same sections over every object above `V`.

No formalization is vendored; the constructions are `AddMonoidHom.codRestrict` applied section by
section, assembled by Mathlib's `PresheafOfModules.homMk`.
-/

public section

universe v v₁ u₁ u

open CategoryTheory Opposite

variable {C : Type u₁} [Category.{v₁} C]

namespace TauCeti

namespace PresheafOfModules

variable {R : Cᵒᵖ ⥤ RingCat.{u}} {M P : _root_.PresheafOfModules.{v} R}

noncomputable section

/-- A morphism of presheaves of modules all of whose sections lie in a submodule `N` of the
target factors through the presheaf of modules attached to `N`. -/
def liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) :
    P ⟶ N.toPresheafOfModules :=
  _root_.PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        (((φ.app U).hom.toAddMonoidHom).codRestrict (N.obj U) (hφ U))
      naturality := by
        intro U V f
        ext x
        apply Subtype.ext
        exact _root_.PresheafOfModules.naturality_apply φ f x }
    (by
      intro U r m
      apply Subtype.ext
      exact (φ.app U).hom.map_smul r m)

@[simp]
lemma liftToSubmodule_app_coe (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) (U : Cᵒᵖ) (s : P.obj U) :
    ((liftToSubmodule N φ hφ).app U s).val = φ.app U s :=
  (rfl)

@[reassoc (attr := simp)]
lemma liftToSubmodule_ι (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.obj U), φ.app U s ∈ N.obj U) :
    liftToSubmodule N φ hφ ≫ N.ι = φ := by
  ext U s
  exact liftToSubmodule_app_coe N φ hφ U s

lemma ι_app_mem (N : M.Submodule) (U : Cᵒᵖ) (s : N.toPresheafOfModules.obj U) :
    N.ι.app U s ∈ N.obj U :=
  s.2

end

end PresheafOfModules

namespace SheafOfModules

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M P : _root_.SheafOfModules.{v} R}

noncomputable section

/-- A morphism of sheaves of modules all of whose sections lie in a submodule `N` of the target
factors through the sheaf of modules attached to `N`. -/
def liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    P ⟶ N.toSheafOfModules :=
  ⟨PresheafOfModules.liftToSubmodule N.toSubmodule φ.val hφ⟩

@[simp]
lemma liftToSubmodule_val_app_coe (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U)
    (U : Cᵒᵖ) (s : P.val.obj U) :
    ((liftToSubmodule N φ hφ).val.app U s).val = φ.val.app U s :=
  (rfl)

@[reassoc (attr := simp)]
lemma liftToSubmodule_ι (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    liftToSubmodule N φ hφ ≫ N.ι = φ :=
  _root_.SheafOfModules.Hom.ext (PresheafOfModules.liftToSubmodule_ι N.toSubmodule φ.val hφ)

lemma ι_val_app_mem (N : M.Submodule) (U : Cᵒᵖ) (s : N.toSheafOfModules.val.obj U) :
    N.ι.val.app U s ∈ N.toSubmodule.obj U :=
  PresheafOfModules.ι_app_mem N.toSubmodule U s

/-- The inclusion of a submodule sheaf is injective on sections. -/
lemma ι_val_app_injective (N : M.Submodule) (U : Cᵒᵖ) :
    Function.Injective (N.ι.val.app U) :=
  Subtype.val_injective

/-- The image of the inclusion on sections is the defining submodule. -/
@[simp]
lemma range_ι_val_app (N : M.Submodule) (U : Cᵒᵖ) :
    Set.range (N.toSubmodule.ι.app U) = N.toSubmodule.obj U := by
  ext s
  exact ⟨fun ⟨t, ht⟩ ↦ ht ▸ ι_val_app_mem N U t, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩

/-- The factorization `liftToSubmodule N φ hφ` is an isomorphism when `φ` is injective on sections
and every section of `N` is in the image of `φ`. -/
lemma isIso_liftToSubmodule (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U)
    (hinj : ∀ U : Cᵒᵖ, Function.Injective (φ.val.app U))
    (hsurj : ∀ (U : Cᵒᵖ) (s : M.val.obj U), s ∈ N.toSubmodule.obj U → ∃ t, φ.val.app U t = s) :
    IsIso (liftToSubmodule N φ hφ) := by
  rw [← isIso_iff_of_reflects_iso _ (_root_.SheafOfModules.forget _)]
  have (U : Cᵒᵖ) : IsIso ((liftToSubmodule N φ hφ).val.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨fun a b hab ↦ hinj U ?_, fun s ↦ ?_⟩
    · simpa only [liftToSubmodule_val_app_coe] using congrArg Subtype.val hab
    · obtain ⟨t, ht⟩ := hsurj U s.1 s.2
      exact ⟨t, Subtype.ext (by simpa only [liftToSubmodule_val_app_coe] using ht)⟩
  exact (_root_.PresheafOfModules.isoMk (fun U ↦ asIso ((liftToSubmodule N φ hφ).val.app U))
    fun _ _ f ↦ (liftToSubmodule N φ hφ).val.naturality f).isIso_hom

namespace Submodule

/-- The inclusion of a submodule of a sheaf of modules into a larger one. The hypothesis is
stated for the underlying submodules of the presheaf of modules, which is what
`SheafOfModules.Submodule.le_iff` says the order on submodules of a sheaf of modules is. -/
def homOfLE {N₁ N₂ : M.Submodule} (h : N₁.toSubmodule ≤ N₂.toSubmodule) :
    N₁.toSheafOfModules ⟶ N₂.toSheafOfModules :=
  ⟨_root_.PresheafOfModules.Submodule.homOfLE h⟩

@[reassoc (attr := simp)]
lemma homOfLE_ι {N₁ N₂ : M.Submodule} (h : N₁.toSubmodule ≤ N₂.toSubmodule) :
    homOfLE h ≫ N₂.ι = N₁.ι :=
  _root_.SheafOfModules.Hom.ext (_root_.PresheafOfModules.Submodule.homOfLE_ι h)

end Submodule

end

end SheafOfModules

end TauCeti

namespace SheafOfModules.Submodule

variable {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}} {M : SheafOfModules.{v} R}

noncomputable section

/-- Two submodules of a sheaf of modules which have the same sections over every object above `V`
give isomorphic sheaves of modules over `V`, compatibly with their inclusions (`overIsoOfEq_hom_ι`,
`overIsoOfEq_inv_ι`). -/
def overIsoOfEq (N₁ N₂ : M.Submodule) (V : C)
    (h : ∀ (W : C) (_ : W ⟶ V), N₁.toSubmodule.obj (op W) = N₂.toSubmodule.obj (op W)) :
    N₁.toSheafOfModules.over V ≅ N₂.toSheafOfModules.over V :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk
      (fun W ↦
        letI := ((N₁.toSheafOfModules.over V).val.obj W).isModule
        letI := ((N₂.toSheafOfModules.over V).val.obj W).isModule
        LinearEquiv.toModuleIso
          (LinearEquiv.ofEq _ _ (h _ W.unop.hom)))
      (fun _ _ _ ↦ rfl)

/-- The inclusion of a submodule remains a monomorphism after restricting to an object. -/
instance instMonoιOver (N : M.Submodule) (V : C) : Mono (N.ι.over V) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  -- `SheafOfModules.forget` sends a morphism to its underlying presheaf morphism `.val` by
  -- definition, and Mathlib has no `forget_map` lemma to rewrite with, so we restate the goal.
  change Mono (N.ι.over V).val
  apply PresheafOfModules.mono_of_injective
  intro W
  exact Subtype.val_injective

/-- The isomorphism `overIsoOfEq` is compatible with the inclusions into `M`. -/
@[reassoc (attr := simp)]
lemma overIsoOfEq_hom_ι (N₁ N₂ : M.Submodule) (V : C)
    (h : ∀ (W : C) (_ : W ⟶ V), N₁.toSubmodule.obj (op W) = N₂.toSubmodule.obj (op W)) :
    (overIsoOfEq N₁ N₂ V h).hom ≫ N₂.ι.over V = N₁.ι.over V := by
  ext W s
  rfl

/-- The inverse of `overIsoOfEq` is compatible with the inclusions into `M`. -/
@[reassoc (attr := simp)]
lemma overIsoOfEq_inv_ι (N₁ N₂ : M.Submodule) (V : C)
    (h : ∀ (W : C) (_ : W ⟶ V), N₁.toSubmodule.obj (op W) = N₂.toSubmodule.obj (op W)) :
    (overIsoOfEq N₁ N₂ V h).inv ≫ N₁.ι.over V = N₂.ι.over V := by
  ext W s
  rfl

end

end SheafOfModules.Submodule
