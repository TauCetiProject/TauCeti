/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import TauCeti.CategoryTheory.FiberedCategory.FiberedInGroupoids

/-!
# The Grothendieck construction of a pseudofunctor with groupoid fibers

The Grothendieck construction `∫ᶜ F` of a pseudofunctor `F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat` whose
fiber categories are groupoids is fibred in groupoids over `𝒮`: its fibers are equivalent to the
categories `F.obj ⟨op S⟩` by Mathlib's `Fiber.inducedFunctor (comp_const F S)`.

## Main declarations

* `CategoryTheory.Pseudofunctor.CoGrothendieck.isFiberedInGroupoids_forget`: the Grothendieck
  construction of a pseudofunctor with groupoid fibers is fibred in groupoids.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Functor Bicategory Opposite

namespace CategoryTheory

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮]

namespace Pseudofunctor.CoGrothendieck

/-- The Grothendieck construction of a pseudofunctor whose fiber categories are groupoids is
fibred in groupoids. The fiber of the projection over `S` is identified with `F.obj ⟨op S⟩` by
Mathlib's equivalence `Fiber.inducedFunctor (comp_const F S)`. -/
instance isFiberedInGroupoids_forget {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat.{v₂, u₂}}
    [∀ S : 𝒮, IsGroupoid (F.obj ⟨op S⟩)] : (forget F).IsFiberedInGroupoids :=
  have (S : 𝒮) : IsGroupoid (Fiber (forget F) S) :=
    isGroupoid_of_reflects_iso (Fiber.inducedFunctor (comp_const F S)).asEquivalence.inverse
  .of_isGroupoid_fiber (forget F)

end Pseudofunctor.CoGrothendieck

end CategoryTheory
