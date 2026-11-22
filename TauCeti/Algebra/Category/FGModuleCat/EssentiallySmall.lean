/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall
public import Mathlib.CategoryTheory.ObjectProperty.Small

/-!
# Essential smallness of finitely generated modules

Mathlib's `Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall` shows that `FGModuleCat.{v} R`
is essentially small in the universe of `R`. This file records the corresponding
`CategoryTheory.ObjectProperty.EssentiallySmall` instance for `ModuleCat.isFG.{v} R`.
-/

public section

namespace TauCeti

open CategoryTheory

universe u v

/-- Finitely generated `R`-modules form an essentially small subcategory in the universe of `R`. -/
instance (R : Type u) [Ring R] : ObjectProperty.EssentiallySmall.{u} (ModuleCat.isFG.{v} R) where
  exists_small_le' :=
    let e := equivSmallModel.{u} (FGModuleCat.{v} R)
    ⟨.ofObj (e.inverse ⋙ (ModuleCat.isFG.{v} R).ι).obj, inferInstance, fun X hX ↦
      ⟨_, ⟨e.functor.obj ⟨X, hX⟩⟩,
        ⟨(ModuleCat.isFG.{v} R).ι.mapIso (e.unitIso.app ⟨X, hX⟩)⟩⟩⟩

end TauCeti
