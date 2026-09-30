/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.Crossing.CrossingConstant

/-!
# The four-element cyclic crossing test

For an auxiliary cyclic group of order four, exactly three elements have order divisible by
two. This identifies the tag proportion as `3 / 4`, rather than the `1 / 4` that results from
counting only a chosen generator. The same count determines the crossing constant after the
automorphism-group factor is included.
-/

public section

namespace TauCeti.NumberField.Chebotarev

/-- In a cyclic group of order four, the three nonidentity elements have order divisible by two. -/
theorem card_taggedElements_two_of_card_four {H : Type*} [Group H] [Fintype H]
    [IsCyclic H] (hH : Nat.card H = 4) :
    (taggedElements (H := H) 2).card = 3 := by
  rw [card_taggedElements_eq_sum_totient, ← Nat.card_eq_fintype_card, hH]
  decide

/-- In the standard model `C₄ = Multiplicative (ZMod 4)`, three elements are tagged for
`f = 2`. -/
theorem card_taggedElements_two_zmod_four :
    (taggedElements (H := Multiplicative (ZMod 4)) 2).card = 3 :=
  card_taggedElements_two_of_card_four (by rw [Nat.card_eq_fintype_card]; decide)

/-- A four-element cyclic auxiliary group contributes three tags, so its crossing constant is
`3 / (4 * #Aut_K(L))`. -/
theorem crossingConstant_two_of_card_four
    (K L : Type*) [CommSemiring K] [Semiring L] [Algebra K L]
    {H : Type*} [Group H] [Fintype H] [IsCyclic H]
    (hH : Nat.card H = 4) :
    crossingConstant K L (H := H) 2 =
      3 / (4 * (Nat.card (L ≃ₐ[K] L) : ℝ)) := by
  rw [crossingConstant_def, card_taggedElements_two_of_card_four hH, hH]
  ring

end TauCeti.NumberField.Chebotarev
