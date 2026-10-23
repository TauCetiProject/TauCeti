/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Isomorphisms and base change of objects over a base

An isomorphism in `Over X` is an isomorphism of the underlying objects. Mathlib records this
for comma categories (`CategoryTheory.Comma.instIsIsoLeft`) and for arrow categories
(`CategoryTheory.Arrow.isIso_left`), but `Over X` is a `def` rather than an abbreviation for
a comma category, so instance search does not see through it to the comma statement. This file
supplies the missing `Over` form, which lets `infer_instance` discharge `IsIso φ.left` goals
that otherwise have to name the forgetful functor by hand.

Base change `Over.pullback f` along `f : T ⟶ S` sends a morphism `g : A ⟶ B` over `S` to the
induced morphism `A ×_S T ⟶ B ×_S T`, which is the pullback of `g` along the projection
`B ×_S T ⟶ B`.

## Main declarations

* `CategoryTheory.Over.isIso_left`: the underlying morphism of an isomorphism over a base is
  an isomorphism.
* `CategoryTheory.Over.isPullback_pullback_map_left`: base change of a morphism over `S` is a
  pullback of it.
-/

public section

open CategoryTheory.Limits

universe v u

namespace CategoryTheory

namespace Over

/-- The underlying morphism of an isomorphism in `Over X` is an isomorphism. -/
instance isIso_left {T : Type u} [Category.{v} T] {X : T} {f g : Over X} (φ : f ⟶ g)
    [IsIso φ] : IsIso φ.left :=
  (Over.forget X).map_isIso φ

/-- Base change along `f : T ⟶ S` of a morphism `g : A ⟶ B` over `S` is the pullback of `g.left`
along the projection `B ×_S T ⟶ B`: the square formed by `A ×_S T ⟶ B ×_S T`, the two first
projections and `g.left` is cartesian. -/
theorem isPullback_pullback_map_left {C : Type u} [Category.{v} C] {S T : C} (f : T ⟶ S)
    [HasPullbacksAlong f] {A B : Over S} (g : A ⟶ B) :
    IsPullback ((Over.pullback f).map g).left (pullback.fst A.hom f) (pullback.fst B.hom f)
      g.left := by
  refine IsPullback.of_right ?_ (by simp) (IsPullback.of_hasPullback B.hom f).flip
  simpa using (IsPullback.of_hasPullback A.hom f).flip

end Over

end CategoryTheory
