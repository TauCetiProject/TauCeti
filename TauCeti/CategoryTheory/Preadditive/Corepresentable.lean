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
# Corepresentable additive functors to abelian groups

Let `G : C ⥤ Ab` be an additive functor on a preadditive category, and suppose that the underlying
functor to types is corepresented by an object `P`, through a natural bijection
`(P ⟶ X) ≃ G(X)`. Since this bijection sends `f` to `G(f)` applied to the image of `𝟙 P`, it is
additive: `CategoryTheory.Functor.CorepresentableBy.homAddEquiv` bundles it as an additive
equivalence. Examples are `Hom(P, -)` itself and the functor of sections over an object of a site,
corepresented by the free abelian sheaf on that object. This is the analogue for corepresentable
functors of Mathlib's `CategoryTheory.Adjunction.homAddEquiv`.
-/

public section

universe t v u

namespace CategoryTheory.Functor.CorepresentableBy

variable {C : Type u} [Category.{v} C] [Preadditive C] {G : C ⥤ AddCommGrpCat.{t}} [G.Additive]
  {P : C} (R : (G ⋙ forget AddCommGrpCat).CorepresentableBy P)

/-- The bijection `(P ⟶ X) ≃ G(X)` of a corepresentation of an additive functor `G : C ⥤ Ab` by
`P`, as an additive equivalence. -/
noncomputable def homAddEquiv (X : C) : (P ⟶ X) ≃+ G.obj X where
  __ := R.homEquiv
  map_add' f f' := by
    simp only [Equiv.toFun_as_coe, R.homEquiv_eq f, R.homEquiv_eq f', R.homEquiv_eq (f + f')]
    exact congrArg (fun g : G.obj P ⟶ G.obj X ↦ g (R.homEquiv (𝟙 P)))
      (G.map_add (f := f) (g := f'))

@[simp]
lemma homAddEquiv_apply {X : C} (f : P ⟶ X) : R.homAddEquiv X f = R.homEquiv f :=
  (rfl)

@[simp]
lemma homAddEquiv_symm_apply {X : C} (x : G.obj X) :
    (R.homAddEquiv X).symm x = R.homEquiv.symm x :=
  (rfl)

end CategoryTheory.Functor.CorepresentableBy
