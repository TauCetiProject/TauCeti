/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.HigmanSims.Orbits

/-!
# The order of the Higman--Sims permutation model

The exact ATLAS model `TauCeti.Sporadic.HS` has order `44352000`. Its stabilizer chain
along `0, 1, 2, 3, 4` has basic-orbit lengths `100, 77, 60, 32, 3` and trivial final
stabilizer. The order theorem combines these established orbit and rigidity results;
it concerns the permutation model, not the abstract group given by the presentation.

## References

* R. A. Wilson, R. A. Parker, J. N. Bray et al., *ATLAS of Finite Group Representations*,
  version 3, representation `HSG1-p100B0`,
  <https://brauer.maths.qmul.ac.uk/Atlas/v3/permrep/HSG1-p100B0>.
* Á. Seress, *Permutation Group Algorithms*, Cambridge Tracts in Mathematics 152,
  Cambridge University Press, 2003, §4.1.
-/

public section

namespace TauCeti.Sporadic

/-- The ATLAS Higman--Sims permutation model has order
`44352000 = 100 * 77 * 60 * 32 * 3`. -/
theorem card_HS : Nat.card HS = 44352000 := by
  rw [HS.card_eq_462000_mul_card_stabilizerChain, HS.card_stabilizerChain_three_eq,
    HS.card_stabilizerChain_four]

end TauCeti.Sporadic
