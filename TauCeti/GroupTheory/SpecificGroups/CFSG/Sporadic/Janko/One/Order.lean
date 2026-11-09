/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Janko.One.Orbits

/-!
# The order of the first Janko permutation model

The exact ATLAS model `TauCeti.Sporadic.J1` has order `175560`. Its stabilizer chain
along `0, 1, 2` has basic-orbit lengths `266, 110, 6` and trivial final stabilizer.
The order concerns this permutation model, not the abstract presented group.
The surjection `exists_surjective_J1` also gives the corresponding lower bound on
the order of the presented group when it is finite.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `J1G1-p266B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/J1G1-p266B0>.
* Á. Seress, *Permutation Group Algorithms*, Cambridge Tracts in Mathematics 152,
  Cambridge University Press, 2003, §4.1.
-/

public section

namespace TauCeti.Sporadic

/-- The ATLAS first Janko permutation model has order `175560 = 266 * 110 * 6`. -/
theorem card_J1 : Nat.card J1 = 175560 := by
  rw [J1.card_eq_29260_mul_card_stabilizerChain, J1.card_stabilizerChain_two]

/-- The presented first Janko group, when finite, has at least `175560` elements.
A surjection alone does not prove finiteness, so the nonzero-cardinality hypothesis
is essential with the convention `Nat.card = 0` for infinite types. -/
theorem le_natCard_group_J1 (h : 0 < Nat.card SporadicName.J1.Group) :
    175560 ≤ Nat.card SporadicName.J1.Group := by
  have := Nat.finite_of_card_ne_zero h.ne'
  obtain ⟨f, hf⟩ := exists_surjective_J1
  exact card_J1 ▸ Nat.card_le_card_of_surjective f hf

end TauCeti.Sporadic
