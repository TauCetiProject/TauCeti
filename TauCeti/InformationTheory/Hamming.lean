module

public import Mathlib.InformationTheory.Hamming

/-!
# Hamming data on disjoint unions

This file records that Hamming weight and distance on a function whose domain is a disjoint union
split as sums over the two coordinate types. These identities let constructions assembled from
independent coordinate blocks reduce their Hamming data to the data of the blocks.
-/

@[expose] public section

namespace TauCeti

variable {ι κ : Type*} {A : Type*}

/-- The Hamming weight of two words combined on a disjoint union is the sum of their weights. -/
@[simp]
theorem hammingNorm_sumElim [Fintype ι] [Fintype κ] [DecidableEq A] [Zero A]
    (x : ι → A) (y : κ → A) :
    hammingNorm (Sum.elim x y) = hammingNorm x + hammingNorm y := by
  simp only [hammingNorm, Finset.card_filter]
  rw [Fintype.sum_sum_type]
  rfl

/-- The Hamming distance between two pairs of words combined on a disjoint union is the sum of
the distances between the respective words. -/
@[simp]
theorem hammingDist_sumElim [Fintype ι] [Fintype κ] [DecidableEq A]
    (x x' : ι → A) (y y' : κ → A) :
    hammingDist (Sum.elim x y) (Sum.elim x' y') =
      hammingDist x x' + hammingDist y y' := by
  simp only [hammingDist, Finset.card_filter]
  rw [Fintype.sum_sum_type]
  rfl

end TauCeti
