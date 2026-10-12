/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Preserves

/-!
# Effective epimorphisms over a base

The forgetful functor `Over X ⥤ T` reflects effective epimorphisms: a morphism `f : A ⟶ B` of
`Over X` whose underlying morphism `f.left` is an effective epimorphism of `T` is an effective
epimorphism of `Over X`. Indeed, two morphisms `g₁ g₂ : Z ⟶ A.left` with
`g₁ ≫ f.left = g₂ ≫ f.left` lie over `X` through the same map `Z ⟶ X`, so a morphism `e : A ⟶ W`
over `X` coequalizing the pairs over `X` that `f` coequalizes also coequalizes them. Hence `e.left`
descends along `f.left`, and the descended morphism lies over `X` because `f.left` is an
epimorphism.

For schemes, Mathlib shows that flat, surjective and quasi-compact morphisms are effective
epimorphisms; with this instance, so are the morphisms of schemes over a base `S` whose underlying
morphisms have these properties.

## Main results

* `CategoryTheory.Over.reflectsEffectiveEpis_forget`: the forgetful functor `Over X ⥤ T` reflects
  effective epimorphisms.
* `CategoryTheory.Over.effectiveEpi_of_effectiveEpi_left`: a morphism over `X` is an effective
  epimorphism when its underlying morphism is.
-/

public section

namespace CategoryTheory.Over

universe v u

variable {T : Type u} [Category.{v} T] {X : T}

/-- **The forgetful functor `Over X ⥤ T` reflects effective epimorphisms.** -/
instance reflectsEffectiveEpis_forget : (Over.forget X).ReflectsEffectiveEpis where
  reflects {A B} f (_ : EffectiveEpi f.left) := by
    -- A morphism `e` over `X` coequalizing the pairs over `X` identified by `f` coequalizes all
    -- pairs of morphisms into `A.left` identified by `f.left`.
    have hdesc {W : Over X} (e : A ⟶ W)
        (h : ∀ {Z : Over X} (g₁ g₂ : Z ⟶ A), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e)
        {Z : T} (g₁ g₂ : Z ⟶ A.left) (hg : g₁ ≫ f.left = g₂ ≫ f.left) :
        g₁ ≫ e.left = g₂ ≫ e.left := by
      have hw : g₂ ≫ A.hom = g₁ ≫ A.hom := by
        rw [← Over.w f, reassoc_of% hg]
      exact congr($(h (Z := Over.mk (g₁ ≫ A.hom)) (Over.homMk g₁) (Over.homMk g₂ hw)
        (Over.OverMorphism.ext hg)).left)
    refine ⟨⟨{ desc e h := Over.homMk (EffectiveEpi.desc f.left e.left (hdesc e h)) ?_,
                fac e h := Over.OverMorphism.ext (EffectiveEpi.fac f.left e.left (hdesc e h)),
                uniq e h m hm := Over.OverMorphism.ext
                  (EffectiveEpi.uniq f.left e.left (hdesc e h) m.left congr($(hm).left)) }⟩⟩
    rw [← cancel_epi f.left, EffectiveEpi.fac_assoc, Over.w e, Over.w f]

/-- **A morphism over `X` is an effective epimorphism when its underlying morphism is.** -/
instance effectiveEpi_of_effectiveEpi_left {A B : Over X} (f : A ⟶ B) [EffectiveEpi f.left] :
    EffectiveEpi f :=
  (Over.forget X).effectiveEpi_of_map f ‹_›

end CategoryTheory.Over
