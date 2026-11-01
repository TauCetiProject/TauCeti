/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.EffectiveEpi.Basic

/-!
# Effective epimorphisms in a slice category

An effective epimorphism remains effective when regarded as a morphism over a fixed base.
Descent on underlying objects respects the structure morphisms by epimorphism cancellation.
No pullbacks are required. This lets descent on carriers be used for group schemes.
-/

public section

open CategoryTheory

namespace CategoryTheory.Over

variable {C : Type*} [Category* C] {S : C}

/-- A morphism in a slice category is effective epi if its underlying morphism is. -/
instance effectiveEpi_of_effectiveEpi_left {X Y : Over S} (f : X ⟶ Y)
    [EffectiveEpi f.left] : EffectiveEpi f := by
  classical
  let he {W : Over S} (e : X ⟶ W)
      (h : ∀ {Z : Over S} (g₁ g₂ : Z ⟶ X), g₁ ≫ f = g₂ ≫ f → g₁ ≫ e = g₂ ≫ e) :
      ∀ {Z : C} (g₁ g₂ : Z ⟶ X.left),
        g₁ ≫ f.left = g₂ ≫ f.left → g₁ ≫ e.left = g₂ ≫ e.left := by
    intro Z g₁ g₂ hg
    have hw : g₂ ≫ X.hom = g₁ ≫ X.hom := by
      rw [← Over.w f, ← Category.assoc, ← Category.assoc, hg]
    exact congrArg (fun k ↦ k.left)
      (h (homMk (U := Over.mk (g₁ ≫ X.hom)) g₁ rfl)
        (homMk g₂ hw) (OverMorphism.ext hg))
  refine ⟨⟨{
    desc := fun {W} e h ↦ homMk (EffectiveEpi.desc f.left e.left (he e h)) ?_
    fac := ?_
    uniq := ?_ }⟩⟩
  · apply (cancel_epi f.left).mp
    simp [← Category.assoc]
  · intro W e h
    exact OverMorphism.ext (EffectiveEpi.fac f.left e.left (he e h))
  · intro W e h m hm
    apply OverMorphism.ext
    exact EffectiveEpi.uniq f.left e.left (he e h) m.left (congrArg (fun k ↦ k.left) hm)

end CategoryTheory.Over
