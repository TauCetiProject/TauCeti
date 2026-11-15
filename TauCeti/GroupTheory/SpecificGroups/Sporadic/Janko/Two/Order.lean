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
The order theorem concerns this permutation model, not the abstract presented group.
Through the surjection `exists_surjective_J2`, the presented second Janko group has at
least `604800` elements whenever it is finite (`TauCeti.Sporadic.le_natCard_group_J2`).

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
@[simp]
theorem card_J2 : Nat.card J2 = 604800 := by
  rw [J2.card_eq_mul_card_stabilizer_zero_one_two, J2.card_stabilizerChain_three]

/-- When finite, the group presented by `SporadicName.J2.presentation` has at least `604800`
elements. The positivity hypothesis excludes infinite groups, for which `Nat.card` takes the junk
value `0`. -/
theorem le_natCard_group_J2 (h : 0 < Nat.card SporadicName.J2.Group) :
    604800 ≤ Nat.card SporadicName.J2.Group := by
  have := Nat.finite_of_card_ne_zero h.ne'
  obtain ⟨f, hf⟩ := exists_surjective_J2
  exact card_J2 ▸ Nat.card_le_card_of_surjective f hf

end TauCeti.Sporadic
