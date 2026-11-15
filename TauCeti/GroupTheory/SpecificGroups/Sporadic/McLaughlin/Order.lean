/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.McLaughlin.Cocliques

/-!
# The order of the McLaughlin permutation model

The exact ATLAS model `TauCeti.Sporadic.McL` has order `898128000`. Its stabilizer chain
along `0, 1, 2, 3, 4, 5` has basic-orbit lengths `275, 112, 81, 36, 5, 2` and trivial final
stabilizer. The order concerns this permutation model, not the abstract group given by the
presentation. Through the surjection `exists_surjective_McL`, the group presented by the
transcribed McLaughlin presentation has at least that many elements whenever it is finite
(`TauCeti.Sporadic.le_natCard_group_McL`).

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `McLG1-p275B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/McLG1-p275B0>.
* Á. Seress, *Permutation Group Algorithms*, Cambridge Tracts in Mathematics 152,
  Cambridge University Press, 2003, §4.1.
-/

public section

namespace TauCeti.Sporadic

/-- The ATLAS McLaughlin permutation model has order
`898128000 = 275 * 112 * 81 * 36 * 5 * 2`. -/
theorem card_McL : Nat.card McL = 898128000 := by
  rw [McL.card_eq_89812800_mul_card_fixingSubgroup, McL.card_fixing_zero_one_two_three]

/-- The group presented by the transcribed McLaughlin presentation, when finite, has at least
`898128000` elements, since it maps onto the model `McL`. Finiteness is a hypothesis: with the
junk value `Nat.card = 0` for infinite types, a surjection alone gives no lower bound. -/
theorem le_natCard_group_McL (h : 0 < Nat.card SporadicName.McL.Group) :
    898128000 ≤ Nat.card SporadicName.McL.Group := by
  have := Nat.finite_of_card_ne_zero h.ne'
  obtain ⟨f, hf⟩ := exists_surjective_McL
  exact card_McL ▸ Nat.card_le_card_of_surjective f hf

end TauCeti.Sporadic
