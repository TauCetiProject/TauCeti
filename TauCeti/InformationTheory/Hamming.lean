/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.Hamming

/-!
# Hamming data on disjoint unions

This file records that Hamming weight and distance on a function whose domain is a disjoint union
split as sums over the two coordinate types. These identities let constructions assembled from
independent coordinate blocks reduce their Hamming data to the data of the blocks.
-/

public section

namespace TauCeti

variable {ι κ : Type*} {β : ι ⊕ κ → Type*}

/-- The Hamming distance between two pairs of words combined on a disjoint union is the sum of
the distances between the respective words. -/
@[simp]
theorem hammingDist_sumElim [Fintype ι] [Fintype κ] [∀ z, DecidableEq (β z)]
    (x x' : ∀ i, β (.inl i)) (y y' : ∀ j, β (.inr j)) :
    hammingDist (Sum.rec (motive := β) x y) (Sum.rec (motive := β) x' y') =
      hammingDist x x' + hammingDist y y' := by
  simp only [hammingDist, Finset.card_filter]
  rw [Fintype.sum_sum_type]

/-- The Hamming weight of two words combined on a disjoint union is the sum of their weights. -/
@[simp]
theorem hammingNorm_sumElim [Fintype ι] [Fintype κ] [∀ z, DecidableEq (β z)]
    [∀ z, Zero (β z)] (x : ∀ i, β (.inl i)) (y : ∀ j, β (.inr j)) :
    hammingNorm (Sum.rec (motive := β) x y) = hammingNorm x + hammingNorm y := by
  simpa only [← hammingDist_zero_right,
    show Sum.rec (motive := β) (0 : ∀ i, β (.inl i)) (0 : ∀ j, β (.inr j)) = 0 by
      funext z
      cases z <;> rfl] using
    hammingDist_sumElim x (0 : ∀ i, β (.inl i)) y (0 : ∀ j, β (.inr j))

end TauCeti
