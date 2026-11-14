/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing

/-!
# Restriction of linear combinations in presheaves of modules

Restriction maps of a presheaf of modules are semilinear over the restriction maps of the
coefficient presheaf and functorial, so restricting a linear combination of restricted sections
gives the corresponding combination with the composite restriction maps.

## Main declarations

* `PresheafOfModules.map_sum_smul_map`: restriction of a linear combination of restricted sections.
* `PresheafOfModulesOfCommRing.map_map_smul`: restriction of a scalar multiple with a restricted
  coefficient.
-/

public section

open CategoryTheory Opposite

universe u v v₁ u₁

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (N : PresheafOfModules.{v} R)

/-- Restricting a linear combination of restricted sections along `h₀` gives the corresponding
combination with the composite restriction maps. -/
theorem map_sum_smul_map {U V₀ V : C} (f₀ : V₀ ⟶ U) (h₀ : V ⟶ V₀)
    {ι : Type*} [Fintype ι] {W : ι → C} (g₀ : ∀ k, V₀ ⟶ W k) (n : ∀ k, N.obj (op (W k)))
    (a : ι → R.obj (op U)) :
    N.map h₀.op (∑ k, R.map f₀.op (a k) • N.map (g₀ k).op (n k)) =
      ∑ k, R.map (h₀ ≫ f₀).op (a k) • N.map (h₀ ≫ g₀ k).op (n k) := by
  refine (map_sum _ _ _).trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  refine (PresheafOfModules.map_smul N h₀.op _ _).trans ?_
  have er : R.map (h₀ ≫ f₀).op (a k) = R.map h₀.op (R.map f₀.op (a k)) := by
    rw [op_comp, Functor.map_comp]
    rfl
  rw [er]
  exact congrArg _ (PresheafOfModules.map_comp_apply N (g₀ k).op h₀.op (n k)).symm

end PresheafOfModules

namespace PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (N : PresheafOfModulesOfCommRing.{v} R)

/-- Restriction of a scalar multiple with a restricted coefficient uses the composite
restriction on the coefficient. -/
lemma map_map_smul {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z)
    (r : R.obj X) (w : N.obj Y) :
    N.map g (R.map f r • w) = R.map (f ≫ g) r • N.map g w := by
  rw [PresheafOfModules.map_smul, Functor.map_comp]
  rfl

end PresheafOfModulesOfCommRing
