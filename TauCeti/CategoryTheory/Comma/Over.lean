/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.StrongEpi

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
`B ×_S T ⟶ B`. For `f : X ⟶ S` and `g : S' ⟶ S`, the two base changes of `X` to an object
`T` over `S'` agree, `T ×_{S'} (S' ×_S X) ≅ T ×_S X` (`pullbackRightPullbackFstIso`), naturally in
`T`.

Factorization through a monomorphism can be checked after base change whenever the projection
to the source is a strong epimorphism. This uses Mathlib's `StrongEpi.llp` and `CommSq.lift`.

## Main declarations

* `CategoryTheory.Over.isIso_left`: the underlying morphism of an isomorphism over a base is
  an isomorphism.
* `CategoryTheory.Over.isPullback_pullback_map_left`: base change of a morphism over `S` is a
  pullback of it.
* `CategoryTheory.Over.exists_factor_thru_pullback_iff`: factorization through a monomorphism
  can be checked after base change if the projection to the source is a strong epimorphism.
* `CategoryTheory.Over.pullbackRightPullbackFstIso_inv_comp_pullback_map`: the identification
  `T ×_S X ≅ T ×_{S'} (S' ×_S X)` is natural in `T` over `S'`.
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

/-- The identification `T ×_S X ≅ T ×_{S'} (S' ×_S X)` of the two base changes of `f : X ⟶ S` to
an object `T` over `S'`, where `T` lies over `S` through `g : S' ⟶ S`, commutes with the morphisms
induced by a morphism `φ : T ⟶ T'` over `S'`. -/
@[reassoc]
theorem pullbackRightPullbackFstIso_inv_comp_pullback_map {C : Type u} [Category.{v} C]
    [HasPullbacks C] {S S' X : C} (f : X ⟶ S) (g : S' ⟶ S) {T T' : Over S'} (φ : T ⟶ T') :
    (pullbackRightPullbackFstIso g f T.hom).inv ≫ ((Over.pullback (pullback.fst g f)).map φ).left =
      ((Over.pullback f).map ((Over.map g).map φ)).left ≫
        (pullbackRightPullbackFstIso g f T'.hom).inv := by
  apply pullback.hom_ext
  · simp
  · apply pullback.hom_ext
    · simp
    · simp

/-- A morphism over `S` factors through a monomorphism if and only if its base change along
`p` does, provided the projection to its source is a strong epimorphism. -/
theorem exists_factor_thru_pullback_iff {C : Type u} [Category.{v} C]
    {S S' : C} (p : S' ⟶ S) [HasPullbacksAlong p]
    {X Y Z : Over S} [StrongEpi (pullback.fst Z.hom p)]
    (i : X ⟶ Y) [Mono i] (f : Z ⟶ Y) :
    (∃ g : (Over.pullback p).obj Z ⟶ (Over.pullback p).obj X,
      g ≫ (Over.pullback p).map i = (Over.pullback p).map f) ↔
      ∃ g : Z ⟶ X, g ≫ i = f := by
  constructor
  · rintro ⟨g, hg⟩
    have sq : CommSq (g.left ≫ pullback.fst X.hom p) (pullback.fst Z.hom p) i.left f.left := by
      constructor
      simpa using congr(($hg).left ≫ pullback.fst Y.hom p)
    refine ⟨Over.homMk sq.lift ?_, ?_⟩
    · simpa only [Category.assoc, i.w, f.w] using congr($(sq.fac_right) ≫ Y.hom)
    · ext1
      exact sq.fac_right
  · rintro ⟨g, rfl⟩
    exact ⟨(Over.pullback p).map g, ((Over.pullback p).map_comp g i).symm⟩

end Over

end CategoryTheory
