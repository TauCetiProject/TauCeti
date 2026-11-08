/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# Factoring a morphism through a submodule of a sheaf of modules

Mathlib's `SheafOfModules.Submodule` packages a submodule of a sheaf of modules together with the
inclusion `N.ι` of the associated sheaf of modules. This file supplies the universal property of
that inclusion, lifting `PresheafOfModules.Submodule.lift` from the underlying presheaves: a
morphism whose sections all land in `N` factors through `N`, uniquely because `N.ι` is a
monomorphism.

## Main declarations

* `SheafOfModules.Submodule.lift`, the factorization itself, with `lift_ι` recording that it does
  factor the given morphism;
* `SheafOfModules.Submodule.isIso_lift`: the factorization is an isomorphism when the morphism is
  injective on sections with image exactly `N`;
* `SheafOfModules.Submodule.homOfLE`, the inclusion of one submodule of a sheaf of modules into a
  larger one;
* `SheafOfModules.Submodule.overIsoOfEq`, the identification over `V` of two submodules with the
  same sections over every object above `V`.
-/

public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M P : SheafOfModules.{v} R}

noncomputable section

/-- A morphism of sheaves of modules all of whose sections lie in a submodule `N` of the target
factors through the sheaf of modules attached to `N`. -/
def lift (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    P ⟶ N.toSheafOfModules :=
  ⟨N.toSubmodule.lift φ.val hφ⟩

/-- On sections, `N.lift φ hφ` followed by the inclusion of `N` is `φ`. -/
@[simp]
lemma lift_val_app_coe (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U)
    (U : Cᵒᵖ) (s : P.val.obj U) :
    ((N.lift φ hφ).val.app U s).val = φ.val.app U s :=
  N.toSubmodule.lift_app_coe φ.val hφ U s

/-- `N.lift φ hφ` factors `φ` through the inclusion `N.ι`. -/
@[reassoc (attr := simp)]
lemma lift_ι (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U) :
    N.lift φ hφ ≫ N.ι = φ :=
  Hom.ext (N.toSubmodule.lift_ι φ.val hφ)

/-- The factorization `N.lift φ hφ` is an isomorphism when `φ` is injective on sections and every
section of `N` is in the image of `φ`. -/
lemma isIso_lift (N : M.Submodule) (φ : P ⟶ M)
    (hφ : ∀ (U : Cᵒᵖ) (s : P.val.obj U), φ.val.app U s ∈ N.toSubmodule.obj U)
    (hinj : ∀ U : Cᵒᵖ, Function.Injective (φ.val.app U))
    (hsurj : ∀ U : Cᵒᵖ, ∀ s ∈ N.toSubmodule.obj U, ∃ t, φ.val.app U t = s) :
    IsIso (N.lift φ hφ) :=
  have : IsIso ((forget R).map (N.lift φ hφ)) := N.toSubmodule.isIso_lift φ.val hφ hinj hsurj
  isIso_of_reflects_iso _ (forget R)

/-- The inclusion of a submodule of a sheaf of modules into a larger one. -/
def homOfLE {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    N₁.toSheafOfModules ⟶ N₂.toSheafOfModules :=
  ⟨PresheafOfModules.Submodule.homOfLE (le_iff.mp h)⟩

/-- The inclusion `homOfLE h` is compatible with the inclusions into `M`. -/
@[reassoc (attr := simp)]
lemma homOfLE_ι {N₁ N₂ : M.Submodule} (h : N₁ ≤ N₂) :
    homOfLE h ≫ N₂.ι = N₁.ι :=
  (rfl)

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
instance instMonoιOver (N : M.Submodule) (V : C) : Mono (N.ι.over V) :=
  (forget _).mono_of_mono_map <| PresheafOfModules.mono_of_injective fun W s t h ↦ by
    -- `N.ι.over V` is the pushforward of `N.ι` along `Over.forget V` (`overFunctor`), so its
    -- sections over `W` are those of `N.ι` over `W.unop.left`.
    have hW (x) : ((forget _).map (N.ι.over V)).app W x = N.toSubmodule.ι.app (op W.unop.left) x :=
      PresheafOfModules.pushforward_map_app_apply (𝟙 _) N.toSubmodule.ι W x
    rw [hW, hW] at h
    exact PresheafOfModules.injective_of_mono N.toSubmodule.ι (op W.unop.left) h

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
