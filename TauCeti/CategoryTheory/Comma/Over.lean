/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Isomorphisms, base change and `Over.star` for objects over a base

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

In a category with binary products, `Over.star X : C ⥤ Over X` sends `Y` to the projection
`X ⨯ Y ⟶ X` and is right adjoint to the forgetful functor `Over.forget X`. A morphism
`f : Y ⟶ Z` goes to `X ⨯ Y ⟶ X ⨯ Z`, which is the base change of `f` along the projection
`X ⨯ Z ⟶ Z`. Hence, if epimorphisms are stable under base change, `Over.star X` preserves
epimorphisms; if moreover `X ⟶ ⊤_ C` is an epimorphism, it also reflects them. Indeed the
projections `X ⨯ Z ⟶ Z` are then epimorphisms, being base changes of `X ⟶ ⊤_ C`, and
`Over.forget X` preserves epimorphisms as a left adjoint. In a topos both hypotheses hold for any
`X` covering the terminal object, so pulling back to the slice over such an `X` is conservative on
epimorphisms. This is how properties defined through epimorphisms, such as repleteness, can be
checked on a slice over a cover.

## Main declarations

* `CategoryTheory.Over.isIso_left`: the underlying morphism of an isomorphism over a base is
  an isomorphism.
* `CategoryTheory.Over.isPullback_pullback_map_left`: base change of a morphism over `S` is a
  pullback of it.
* `CategoryTheory.Over.pullbackRightPullbackFstIso_inv_comp_pullback_map`: the identification
  `T ×_S X ≅ T ×_{S'} (S' ×_S X)` is natural in `T` over `S'`.
* `CategoryTheory.Over.preservesEpimorphisms_star`: `Over.star X` preserves epimorphisms when
  they are stable under base change.
* `CategoryTheory.Over.reflectsEpimorphisms_star`: `Over.star X` moreover reflects epimorphisms
  when `X ⟶ ⊤_ C` is an epimorphism.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  proof of Lemma 3.1.3.
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

/-- If epimorphisms are stable under base change, then `Over.star X` preserves epimorphisms: it
sends `f : Y ⟶ Z` to `X ⨯ Y ⟶ X ⨯ Z`, a base change of `f`. -/
instance preservesEpimorphisms_star {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] (X : C) :
    (star X).PreservesEpimorphisms where
  preserves {Y Z} f _ := by
    -- Mathlib's square exhibits `Y ⨯ X ⟶ Z ⨯ X` as a base change of `f`; swap the factors.
    have h : IsPullback (prod.snd : X ⨯ Y ⟶ Y) (prod.map (𝟙 X) f) f prod.snd :=
      (IsPullback.of_prod_fst_with_id f X).of_iso (prod.braiding Y X) (Iso.refl _)
        (prod.braiding Z X) (Iso.refl _) (by simp) (by ext <;> simp) (by simp) (by simp)
    have : Epi (prod.map (𝟙 X) f) := MorphismProperty.of_isPullback
      (P := MorphismProperty.epimorphisms C) h (MorphismProperty.epimorphisms.infer_property f)
    -- `star_map_left` identifies the underlying morphism with `prod.map (𝟙 X) f`, between the
    -- objects `((star X).obj Y).left` and `((star X).obj Z).left`, which are `X ⨯ Y` and `X ⨯ Z`
    -- by definition (`star_obj_left`).
    exact epi_of_epi_left _ (hk := by simp only [star_map_left]; exact this)

/-- If epimorphisms are stable under base change and `X ⟶ ⊤_ C` is an epimorphism, then
`Over.star X` reflects epimorphisms. -/
instance reflectsEpimorphisms_star {C : Type u} [Category.{v} C] [HasBinaryProducts C]
    [HasTerminal C] [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] (X : C)
    [Epi (terminal.from X)] : (star X).ReflectsEpimorphisms where
  reflects {Y Z} f _ := by
    -- The counit of `forget X ⊣ star X` at `Z` is the projection `X ⨯ Z ⟶ Z`, a base change of
    -- `X ⟶ ⊤_ C`. By naturality of the counit, `counit_Y ≫ f` is then an epimorphism, and hence
    -- so is `f`.
    have : Epi ((forgetAdjStar X).counit.app Z) := by
      rw [forgetAdjStar_counit_app]
      exact MorphismProperty.of_isPullback (P := MorphismProperty.epimorphisms C)
        (IsPullback.of_hasBinaryProduct' X Z) (MorphismProperty.epimorphisms.infer_property _)
    have := epi_comp' ((forget X).map_epi ((star X).map f)) this
    exact epi_of_epi_fac ((forgetAdjStar X).counit_naturality f).symm

end Over

end CategoryTheory
