/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Yoneda

/-!
# Corepresentations of additive functors to `Ab`

For an additive functor `G : C ⥤ Ab` corepresented by an object `P` of a preadditive category,
the bijection `(P ⟶ X) ≃ G(X)` of the corepresentation is additive: it preserves zero, and so does
its inverse, which is moreover additive.

## Main results

* `CategoryTheory.Functor.CorepresentableBy.homEquiv_zero` and
  `CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_zero`: the corepresentation and its
  inverse preserve zero.
* `CategoryTheory.Functor.CorepresentableBy.homEquiv_symm_add`: the inverse of the
  corepresentation is additive.
-/

public section

open CategoryTheory

universe t v u

namespace CategoryTheory.Functor.CorepresentableBy

variable {C : Type u} [Category.{v} C] [Preadditive C] {G : C ⥤ AddCommGrpCat.{t}} [G.Additive]
  {P : C} (R : (G ⋙ forget AddCommGrpCat).CorepresentableBy P)

/-- The corepresentation of an additive functor `G : C ⥤ Ab` sends the zero morphism to zero. -/
lemma homEquiv_zero {X : C} : R.homEquiv (0 : P ⟶ X) = (0 : G.obj X) := by
  rw [R.homEquiv_eq, Functor.comp_map, G.map_zero]
  rfl

/-- The inverse of the corepresentation of an additive functor `G : C ⥤ Ab` sends zero to the zero
morphism. -/
lemma homEquiv_symm_zero {X : C} : R.homEquiv.symm (0 : G.obj X) = 0 :=
  R.homEquiv.symm_apply_eq.2 R.homEquiv_zero.symm

/-- The inverse of the corepresentation `(P ⟶ X) ≃ G(X)` of an additive functor `G : C ⥤ Ab` is
additive. -/
lemma homEquiv_symm_add {X : C} (x y : G.obj X) :
    R.homEquiv.symm (x + y) = R.homEquiv.symm x + R.homEquiv.symm y := by
  have h (z : G.obj X) : G.map (R.homEquiv.symm z) (R.homEquiv (𝟙 P)) = z :=
    (R.homEquiv_eq _).symm.trans (R.homEquiv.apply_symm_apply z)
  rw [R.homEquiv.symm_apply_eq, R.homEquiv_eq, Functor.comp_map, G.map_add]
  exact (congrArg₂ (· + ·) (h x) (h y)).symm

end CategoryTheory.Functor.CorepresentableBy
