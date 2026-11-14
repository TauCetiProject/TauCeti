/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-!
# Pushforwards of presheaves of modules

Mathlib's `PresheafOfModules.pushforward₀ F R` reindexes a presheaf of `R`-modules along a functor
`F`. On morphisms it keeps the components: `TauCeti.PresheafOfModules.pushforward₀_map_app_apply`
records that the component at `X` of the pushforward of `α` is the component of `α` at the image of
`X`.

The pushforward `PresheafOfModules.pushforward φ` along a morphism of presheaves of rings
`φ : S ⟶ F.op ⋙ R` is exact: it preserves finite limits
(`TauCeti.PresheafOfModules.preservesFiniteLimits_pushforward`) and finite colimits
(`TauCeti.PresheafOfModules.preservesFiniteColimits_pushforward`), because limits and colimits of
presheaves of modules are computed on the underlying presheaves of abelian groups, where the
pushforward is precomposition with `F`. In particular it preserves homology, by Mathlib's
`CategoryTheory.Functor.preservesHomologyOfExact`, and is additive
(`TauCeti.PresheafOfModules.additive_pushforward`).
-/

public section

open CategoryTheory Limits Opposite

universe v v₁ v₂ u₁ u₂ u

namespace TauCeti.PresheafOfModules

open _root_.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
  {R : Dᵒᵖ ⥤ RingCat.{u}}

/-- The pushforward along `F` of a morphism `α` of presheaves of modules has, at `X`, the
component of `α` at the image of `X`.

The element is taken in the domain of the pushed-forward component, so that the lemma rewrites
goals about components of pushed-forward morphisms; an element of `M.obj (op (F.obj X.unop))` may
be passed as well, since the two modules are definitionally equal.

The `simp↓` attribute rewrites the component before simp normalizes its base ring
`(F.op ⋙ R).obj X` inside the implicit arguments of the coercion; ordinary `simp` would
normalize that ring first and prevent this lemma from matching. -/
@[simp↓]
theorem pushforward₀_map_app_apply {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : ((pushforward₀ F R).obj M).obj X) :
    ((pushforward₀ F R).map α).app X m = α.app (op (F.obj X.unop)) m :=
  rfl

variable {F} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- The pushforward of presheaves of modules preserves finite limits: forgetting the module
structure creates them, and on underlying presheaves of abelian groups the pushforward is
precomposition with `F`. -/
instance preservesFiniteLimits_pushforward : PreservesFiniteLimits (pushforward.{v} φ) := by
  -- Componentwise, the composite with `toPresheaf S` is evaluation of `toPresheaf R` at the image.
  have : PreservesFiniteLimits (pushforward.{v} φ ⋙ toPresheaf S) := ⟨fun J _ _ ↦
    preservesLimitsOfShape_of_evaluation _ J fun X ↦
      inferInstanceAs (PreservesLimitsOfShape J
        (toPresheaf R ⋙ (CategoryTheory.evaluation _ _).obj (op (F.obj X.unop))))⟩
  exact preservesFiniteLimits_of_reflects_of_preserves _ (toPresheaf S)

/-- The pushforward of presheaves of modules preserves finite colimits: forgetting the module
structure creates them, and on underlying presheaves of abelian groups the pushforward is
precomposition with `F`. -/
instance preservesFiniteColimits_pushforward : PreservesFiniteColimits (pushforward.{v} φ) := by
  -- Componentwise, the composite with `toPresheaf S` is evaluation of `toPresheaf R` at the image.
  have : PreservesFiniteColimits (pushforward.{v} φ ⋙ toPresheaf S) := ⟨fun J _ _ ↦
    preservesColimitsOfShape_of_evaluation _ J fun X ↦
      inferInstanceAs (PreservesColimitsOfShape J
        (toPresheaf R ⋙ (CategoryTheory.evaluation _ _).obj (op (F.obj X.unop))))⟩
  exact preservesFiniteColimits_of_reflects_of_preserves _ (toPresheaf S)

/-- The pushforward of presheaves of modules is additive. -/
instance additive_pushforward : (pushforward.{v} φ).Additive :=
  (pushforward.{v} φ).additive_of_preserves_binary_products

end TauCeti.PresheafOfModules
