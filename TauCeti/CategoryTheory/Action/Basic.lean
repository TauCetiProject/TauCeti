/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Action.Concrete

/-!
# Orbit maps of `G`-sets

For a monoid `G`, a point `x` of a `G`-set `A` has an orbit map `a ↦ a • x`, which is a map of
`G`-sets out of the left regular `G`-set `Action.leftRegular G`. Evaluation at `1` inverts this
construction, so the left regular `G`-set corepresents the forgetful functor to types. These maps
are the basic tool for testing statements about `G`-sets on points.

## Main declarations

* `Action.hom_comm_apply`: a map of `G`-sets commutes with the actions on underlying elements.
* `CategoryTheory.Action.leftRegularHom`: the orbit map of a point of a `G`-set, as a map of
  `G`-sets out of the left regular `G`-set.
* `CategoryTheory.Action.leftRegularHom_injective`: the orbit map is injective in the point.
* `CategoryTheory.Action.leftRegularHom_comp`: the orbit map is natural in the `G`-set.
* `CategoryTheory.Action.leftRegularHom_hom_one`: every map out of the left regular `G`-set is the
  orbit map of the image of `1`.
-/

public section

open CategoryTheory

universe u

variable {G : Type u} [Monoid G]

/-- The orbit map `a ↦ a • x` of a point `x` of a `G`-set `A`, as a map of `G`-sets from the left
regular `G`-set to `A`. -/
def CategoryTheory.Action.leftRegularHom {A : Action (Type u) G} (x : ToType A) :
    Action.leftRegular G ⟶ A where
  hom := ↾(fun a : G => a • x)
  comm g := by ext a; exact mul_smul g a x

@[simp]
theorem CategoryTheory.Action.leftRegularHom_hom_apply {A : Action (Type u) G}
    (x : ToType A) (a : G) :
    (Action.leftRegularHom x).hom a = a • x :=
  by
    -- Unfold the unexposed constructor once to establish its public computation rule.
    change a • x = a • x
    rfl

/-- A map of `G`-sets commutes with the actions on underlying elements. -/
theorem Action.hom_comm_apply {A B : Action (Type u) G} (f : A ⟶ B) (g : G) (x : A.V) :
    f.hom (A.ρ g x) = B.ρ g (f.hom x) :=
  ConcreteCategory.congr_hom (f.comm g) x

/-- Composing the orbit map of `x` with a map of `G`-sets `f` gives the orbit map of `f x`. -/
@[simp]
theorem CategoryTheory.Action.leftRegularHom_comp {A B : Action (Type u) G}
    (x : ToType A) (f : A ⟶ B) :
    Action.leftRegularHom x ≫ f = Action.leftRegularHom (f.hom x) := by
  ext a
  exact (congrArg f.hom (Action.leftRegularHom_hom_apply x a)).trans
    ((Action.hom_comm_apply f a x).trans (Action.leftRegularHom_hom_apply (f.hom x) a).symm)

/-- Every map of `G`-sets out of the left regular `G`-set is the orbit map of the image of `1`. -/
@[simp]
theorem CategoryTheory.Action.leftRegularHom_hom_one {A : Action (Type u) G}
    (f : Action.leftRegular G ⟶ A) : Action.leftRegularHom (f.hom (1 : G)) = f := by
  ext a
  exact (Action.leftRegularHom_hom_apply (f.hom (1 : G)) a).trans
    ((Action.hom_comm_apply f a (1 : G)).symm.trans (congrArg f.hom (mul_one (M := G) a)))

/-- A point of a `G`-set is determined by its orbit map, as the value at `1`. -/
theorem CategoryTheory.Action.leftRegularHom_injective {A : Action (Type u) G} :
    Function.Injective (Action.leftRegularHom : ToType A → (Action.leftRegular G ⟶ A)) :=
  fun x y h ↦ by
    simpa using ((Action.leftRegularHom_hom_apply x 1).symm.trans
      (congrArg (fun f ↦ f.hom (1 : G)) h)).trans (Action.leftRegularHom_hom_apply y 1)
