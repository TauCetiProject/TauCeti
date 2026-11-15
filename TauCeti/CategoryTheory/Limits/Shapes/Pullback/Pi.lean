/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Products of morphisms that are invertible away from one index

Let `g i : X i ⟶ Y i` be a family of morphisms that are isomorphisms for every index `i ≠ i₀`.
Then the square formed by `Pi.map g`, `g i₀` and the two projections onto the factor `i₀` is a
pullback square (`CategoryTheory.IsPullback.of_pi_map_of_isIso`). Thus `Pi.map g` is a base change
of `g i₀`, and any property of morphisms stable under base change passes from `g i₀` to
`Pi.map g`.

This is the analogue for arbitrary products of Mathlib's
`CategoryTheory.IsPullback.of_prod_fst_with_id` for `prod.map f (𝟙 X)`. It shows that the
transition maps of the tower `CategoryTheory.Limits.SequentialProduct.functorMap`, which change
one factor of a product at a time, are epimorphisms whenever the morphisms `f n` defining the
tower are epimorphisms and the category's epimorphisms are stable under base change.
-/

public section

universe w v u

open CategoryTheory Limits

namespace CategoryTheory.IsPullback

variable {C : Type u} [Category.{v} C] {ι : Type w} {X Y : ι → C} [HasProduct X] [HasProduct Y]

/-- If `g i : X i ⟶ Y i` is an isomorphism for every `i ≠ i₀`, then `Pi.map g` is the base change
of `g i₀` along the projection `∏ Y ⟶ Y i₀`. -/
theorem of_pi_map_of_isIso (g : ∀ i, X i ⟶ Y i) (i₀ : ι) (hg : ∀ i, i ≠ i₀ → IsIso (g i)) :
    IsPullback (Pi.π X i₀) (Limits.Pi.map g) (g i₀) (Pi.π Y i₀) := by
  classical
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ Pi.lift fun i ↦
    if h : i = i₀ then h ▸ s.fst else
      haveI := hg i h; s.snd ≫ Pi.π Y i ≫ inv (g i)) ?_ ?_ ?_⟩⟩
  · intro s
    simp
  · intro s
    refine Pi.hom_ext _ _ fun i ↦ ?_
    by_cases h : i = i₀
    · subst h
      simpa using s.condition
    · simp [h]
  · intro s m h₁ h₂
    refine Pi.hom_ext _ _ fun i ↦ ?_
    by_cases h : i = i₀
    · subst h
      simpa using h₁
    · have := hg i h
      simp [h, ← h₂]

end CategoryTheory.IsPullback
