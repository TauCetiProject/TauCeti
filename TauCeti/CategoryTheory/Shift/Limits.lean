/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Shift.Basic

/-!
# Limits and colimits under shift functors

Given a category `T` with a shift by `A`, a family `f : J → T` with a coproduct `∐ f`, and a
degree `a : A` whose shift functor `shiftFunctor T a` preserves that coproduct (automatic when
`A` is an `AddGroup`, such as `ℤ`), the shifted cofan over `fun j ↦ (f j)⟦a⟧` with vertex
`(∐ f)⟦a⟧` and inclusions `(Sigma.ι f j)⟦a⟧'` is a colimit cofan
(`TauCeti.isColimitShiftedCoproductCofan`).

## Main definitions

* `TauCeti.isColimitShiftedCoproductCofan`: colimit cofan witness for a shifted coproduct.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace TauCeti

/-- Given a family `f : J → T` with a coproduct `∐ f` and a shift functor `shiftFunctor T a`
preserving this coproduct (for instance, for any group-indexed shift such as `ℤ`), the shifted
cofan with vertex `(∐ f)⟦a⟧` and inclusions `(Sigma.ι f j)⟦a⟧'` is a colimit cofan. -/
def isColimitShiftedCoproductCofan {T : Type*} [Category* T] {A : Type*} [AddMonoid A]
    [HasShift T A] {J : Type*} (f : J → T) (a : A) [HasCoproduct f]
    [PreservesColimit (Discrete.functor f) (shiftFunctor T a)] :
    IsColimit (Cofan.mk (f := fun j ↦ (f j)⟦a⟧) ((∐ f)⟦a⟧) fun j ↦ (Sigma.ι f j)⟦a⟧') :=
  (isColimitMapCoconeCofanMkEquiv (shiftFunctor T a) f (Sigma.ι f)).toFun
    (isColimitOfPreserves (shiftFunctor T a) (coproductIsCoproduct f))

end TauCeti
