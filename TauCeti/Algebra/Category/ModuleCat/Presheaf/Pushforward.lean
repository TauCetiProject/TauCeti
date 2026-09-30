/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward

/-!
# Components of pushforwards of morphisms of presheaves of modules

Mathlib's `PresheafOfModules.pushforward₀ F R` reindexes a presheaf of `R`-modules along a functor
`F`. On morphisms it keeps the components: `TauCeti.PresheafOfModules.pushforward₀_map_app_apply`
records that the component at `X` of the pushforward of `α` is the component of `α` at the image of
`X`.
-/

public section

open CategoryTheory Opposite

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

This is not a simp lemma: simp rewrites the base ring `(F.op ⋙ R).obj X` of the component to
`R.obj (op (F.obj X.unop))` inside the implicit arguments of the coercion, so the left-hand side
has no simp normal form. -/
theorem pushforward₀_map_app_apply {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : ((pushforward₀ F R).obj M).obj X) :
    ((pushforward₀ F R).map α).app X m = α.app (op (F.obj X.unop)) m :=
  rfl

end TauCeti.PresheafOfModules
