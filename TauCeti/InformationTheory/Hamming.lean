/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.Hamming

/-!
# Hamming data on disjoint unions and under coordinate reindexing

This file records that Hamming weight and distance on a function whose domain is a disjoint union
split as sums over the two coordinate types. These identities let constructions assembled from
independent coordinate blocks reduce their Hamming data to the data of the blocks.

It also proves that Hamming distance and Hamming weight are invariant under relabelling a finite
coordinate type along an equivalence.
-/

public section

namespace TauCeti

variable {ι κ : Type*} {β : ι ⊕ κ → Type*}

/-- The Hamming distance between two pairs of words combined on a disjoint union is the sum of
the distances between the respective words. -/
@[simp]
theorem hammingDist_sumRec [Fintype ι] [Fintype κ] [∀ z, DecidableEq (β z)]
    (x x' : ∀ i, β (.inl i)) (y y' : ∀ j, β (.inr j)) :
    hammingDist (Sum.rec (motive := β) x y) (Sum.rec (motive := β) x' y') =
      hammingDist x x' + hammingDist y y' := by
  simp only [hammingDist, Finset.card_filter]
  rw [Fintype.sum_sum_type]

/-- The Hamming weight of two words combined on a disjoint union is the sum of their weights. -/
@[simp]
theorem hammingNorm_sumRec [Fintype ι] [Fintype κ] [∀ z, DecidableEq (β z)]
    [∀ z, Zero (β z)] (x : ∀ i, β (.inl i)) (y : ∀ j, β (.inr j)) :
    hammingNorm (Sum.rec (motive := β) x y) = hammingNorm x + hammingNorm y := by
  have sumRec_zero :
      Sum.rec (motive := β) (0 : ∀ i, β (.inl i)) (0 : ∀ j, β (.inr j)) = 0 := by
    funext z
    cases z <;> rfl
  simpa only [← hammingDist_zero_right, sumRec_zero] using
    hammingDist_sumRec x (0 : ∀ i, β (.inl i)) y (0 : ∀ j, β (.inr j))

/-- The Hamming distance between two pairs of words over a common alphabet, combined on a disjoint
union, is the sum of the distances between the respective words. -/
@[simp]
theorem hammingDist_sumElim {A : Type*} [Fintype ι] [Fintype κ] [DecidableEq A]
    (x x' : ι → A) (y y' : κ → A) :
    hammingDist (Sum.elim x y) (Sum.elim x' y') = hammingDist x x' + hammingDist y y' :=
  hammingDist_sumRec (β := fun _ ↦ A) x x' y y'

/-- The Hamming weight of two words over a common alphabet, combined on a disjoint union, is the
sum of their weights. -/
@[simp]
theorem hammingNorm_sumElim {A : Type*} [Fintype ι] [Fintype κ] [DecidableEq A] [Zero A]
    (x : ι → A) (y : κ → A) :
    hammingNorm (Sum.elim x y) = hammingNorm x + hammingNorm y :=
  hammingNorm_sumRec (β := fun _ ↦ A) x y

end TauCeti

namespace Equiv

variable {α ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq α]

/-- Relabelling coordinates along an equivalence preserves the Hamming distance. -/
theorem hammingDist_comp (e : κ ≃ ι) (x y : ι → α) :
    hammingDist (x ∘ e) (y ∘ e) = hammingDist x y := by
  simp only [hammingDist, Function.comp_apply]
  exact Finset.card_equiv e (by simp)

/-- Relabelling coordinates along an equivalence preserves the Hamming weight. -/
theorem hammingNorm_comp [Zero α] (e : κ ≃ ι) (x : ι → α) :
    hammingNorm (x ∘ e) = hammingNorm x := by
  simp only [hammingNorm, Function.comp_apply]
  exact Finset.card_equiv e (by simp)

end Equiv
