/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Epimorphisms and the functor `Over.star`

In a category with binary products, `Over.star X : C ⥤ Over X` sends `Y` to the projection
`X ⨯ Y ⟶ X` and is right adjoint to the forgetful functor `Over.forget X`. A morphism
`f : Y ⟶ Z` goes to `X ⨯ Y ⟶ X ⨯ Z`, which is the base change of `f` along the projection
`X ⨯ Z ⟶ Z`. Hence:

* if epimorphisms are stable under base change, `Over.star X` preserves epimorphisms
  (`CategoryTheory.Over.preservesEpimorphisms_star`);
* if moreover `X ⟶ ⊤_ C` is an epimorphism, `Over.star X` reflects epimorphisms
  (`CategoryTheory.Over.reflectsEpimorphisms_star`). Indeed the projections `X ⨯ Z ⟶ Z` are then
  epimorphisms, being base changes of `X ⟶ ⊤_ C`, and `Over.forget X` preserves epimorphisms as a
  left adjoint.

In a topos both hypotheses hold for any `X` covering the terminal object, so pulling back to the
slice over such an `X` is conservative on epimorphisms. This is how properties defined through
epimorphisms, such as repleteness, can be checked on a slice over a cover.

## References

* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015),
  proof of Lemma 3.1.3.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Over

variable {C : Type u} [Category.{v} C] [HasBinaryProducts C]

/-- If epimorphisms are stable under base change, then `Over.star X` preserves epimorphisms: it
sends `f : Y ⟶ Z` to `X ⨯ Y ⟶ X ⨯ Z`, a base change of `f`. -/
instance preservesEpimorphisms_star [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange]
    (X : C) : (star X).PreservesEpimorphisms where
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
instance reflectsEpimorphisms_star [HasTerminal C]
    [(MorphismProperty.epimorphisms C).IsStableUnderBaseChange] (X : C) [Epi (terminal.from X)] :
    (star X).ReflectsEpimorphisms where
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

end CategoryTheory.Over
