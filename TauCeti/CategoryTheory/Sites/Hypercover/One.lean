/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.Hypercover.One

/-!
# Basic extensionality for `PreOneHypercover` and `OneHypercover`

This file complements `Mathlib.CategoryTheory.Sites.Hypercover.One` by providing a pointwise
extensionality lemma for pre-`1`-hypercovers sharing the same index types and injectivity of
`OneHypercover.toPreOneHypercover`.

## Main results

* `CategoryTheory.PreOneHypercover.ext_sameIndex`: pointwise extensionality for two
  `PreOneHypercover`s with equal index types `I₀` and `I₁`.
* `CategoryTheory.GrothendieckTopology.OneHypercover.toPreOneHypercover_injective`: two
  `J`-`1`-hypercovers with equal underlying pre-`1`-hypercovers are equal.
-/

public section

universe w v u

namespace CategoryTheory.PreOneHypercover

/-- Pointwise extensionality for two `PreOneHypercover`s sharing the same index types `I₀` and
`I₁`, discharging the commutativity field `w` by proof irrelevance. -/
lemma ext_sameIndex {C : Type u} [Category.{v} C] {S : C}
    {I₀ : Type w} {X X' : I₀ → C} {f : ∀ i, X i ⟶ S} {f' : ∀ i, X' i ⟶ S}
    {I₁ : I₀ → I₀ → Type w}
    {Y Y' : ∀ ⦃i₁ i₂⦄, I₁ i₁ i₂ → C}
    {p₁ : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), Y k ⟶ X i₁}
    {p₁' : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), Y' k ⟶ X' i₁}
    {p₂ : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), Y k ⟶ X i₂}
    {p₂' : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), Y' k ⟶ X' i₂}
    {w : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), p₁ k ≫ f i₁ = p₂ k ≫ f i₂}
    {w' : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), p₁' k ≫ f' i₁ = p₂' k ≫ f' i₂}
    (hX : ∀ i, X i = X' i) (hf : ∀ i, f i ≍ f' i)
    (hY : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), Y k = Y' k)
    (hp₁ : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), p₁ k ≍ p₁' k)
    (hp₂ : ∀ ⦃i₁ i₂⦄ (k : I₁ i₁ i₂), p₂ k ≍ p₂' k) :
    (⟨⟨I₀, X, f⟩, I₁, Y, p₁, p₂, w⟩ : PreOneHypercover S) =
      ⟨⟨I₀, X', f'⟩, I₁, Y', p₁', p₂', w'⟩ := by
  have hX' : X = X' := funext hX
  have hY' : Y = Y' := funext fun _ ↦ funext fun _ ↦ funext fun k ↦ hY k
  subst hX' hY'
  obtain rfl : f = f' := funext fun i ↦ eq_of_heq (hf i)
  obtain rfl : p₁ = p₁' := funext fun _ ↦ funext fun _ ↦ funext fun k ↦ eq_of_heq (hp₁ k)
  obtain rfl : p₂ = p₂' := funext fun _ ↦ funext fun _ ↦ funext fun k ↦ eq_of_heq (hp₂ k)
  rfl

end CategoryTheory.PreOneHypercover

namespace CategoryTheory.GrothendieckTopology.OneHypercover

/-- Two `J`-`1`-hypercovers of `S` with equal underlying pre-`1`-hypercovers are equal. -/
lemma toPreOneHypercover_injective {C : Type u} [Category.{v} C]
    {J : GrothendieckTopology C} {S : C} :
    Function.Injective (toPreOneHypercover : J.OneHypercover.{w} S → PreOneHypercover.{w} S) :=
  fun ⟨_, _, _⟩ ⟨_, _, _⟩ h ↦ by cases h; rfl

end CategoryTheory.GrothendieckTopology.OneHypercover
