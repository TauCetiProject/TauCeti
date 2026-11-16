/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Janko.Two.Orbits

/-!
# The order of the second Janko permutation model

The exact ATLAS model `TauCeti.Sporadic.J2` has order `604800`. Its stabilizer chain
along `0, 1, 2, 3` has basic-orbit lengths `100, 63, 24, 4` and trivial final stabilizer.
The order theorem combines these established orbit and rigidity results; it concerns the
permutation model, not the abstract group given by the presentation. Through the surjection
`exists_surjective_J2`, the group presented by the transcribed second Janko presentation
has at least that many elements whenever it is finite (`TauCeti.Sporadic.le_natCard_group_J2`).

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `J2G1-p100B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/J2G1-p100B0>.
* Á. Seress, *Permutation Group Algorithms*, Cambridge Tracts in Mathematics 152,
  Cambridge University Press, 2003, §4.1.
-/

public section

namespace TauCeti.Sporadic

/-- The ATLAS second Janko permutation model has order `604800 = 100 * 63 * 24 * 4`. -/
theorem card_J2 : Nat.card J2 = 604800 := by
  rw [J2.card_eq_mul_card_stabilizer_zero_one_two, J2.card_stabilizerChain_three]

/-- The group presented by the transcribed second Janko presentation, when finite, has at least
`604800` elements, since it maps onto the model `J2`. Finiteness is a hypothesis: with the junk
value `Nat.card = 0` for infinite types, a surjection alone gives no lower bound. -/
theorem le_natCard_group_J2 (h : 0 < Nat.card SporadicName.J2.Group) :
    604800 ≤ Nat.card SporadicName.J2.Group := by
  have := Nat.finite_of_card_ne_zero h.ne'
  obtain ⟨f, hf⟩ := exists_surjective_J2
  exact card_J2 ▸ Nat.card_le_card_of_surjective f hf

end TauCeti.Sporadic
