/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Conway.Three.Orbits

/-!
# The order of the third Conway permutation model

The degree-276 ATLAS permutation model `TauCeti.Sporadic.Co3` has order
`495766656000 = 2¹⁰ · 3⁷ · 5³ · 7 · 11 · 23`. Along the base `0, 1, 2, 3, 4, 5` its stabilizer
chain has basic-orbit lengths `276, 275, 162, 56, 45, 16` and trivial six-point stabilizer, as
proved in `TauCeti.GroupTheory.SpecificGroups.Sporadic.Conway.Three.Orbits`. The order theorem
here concerns this concrete permutation model rather than the group defined by a finite
presentation.

## Main declarations

* `TauCeti.Sporadic.card_Co3`: the permutation model `Co3` has order `495766656000`.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `Co3G1-p276B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/Co3G1-p276B0>.
* Á. Seress, *Permutation Group Algorithms*, Cambridge Tracts in Mathematics 152,
  Cambridge University Press, 2003, §4.1.
-/

public section

namespace TauCeti.Sporadic

/-- The degree-276 ATLAS permutation model of the third Conway group has order
`495766656000 = 276 * 275 * 162 * 56 * 45 * 16`. -/
theorem card_Co3 : Nat.card Co3 = 495766656000 := by
  rw [Co3.card_eq_12295800_mul_card_stabilizerChain, Co3.card_stabilizerChain_three]

end TauCeti.Sporadic
