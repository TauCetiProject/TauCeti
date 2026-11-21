/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Conway.Three.Order
public import TauCeti.GroupTheory.SpecificGroups.Sporadic.Conway.Three.Presentation

/-!
# Order lower bound for the third Conway presentation

The group defined by Djoković's presentation (13.1) surjects onto the degree-276 model
from the ATLAS of Finite Group Representations, version 3 (`Co3G1-p276B0`). The order of
that model therefore bounds the order of the presented group from below when the latter
is finite. This supplies the lower bound for a comparison with an independent upper bound
on the order of the presented group; it does not establish finiteness.
-/

public section

namespace TauCeti.Sporadic

/-- When finite, the group defined by `SporadicName.Co3.presentation` has at least
`495766656000` elements. The hypothesis excludes the junk value `0` of `Nat.card`
on infinite groups. -/
theorem le_natCard_group_Co3 (h : 0 < Nat.card SporadicName.Co3.Group) :
    495766656000 ≤ Nat.card SporadicName.Co3.Group := by
  obtain ⟨f, hf⟩ := exists_surjective_Co3
  exact Nat.le_of_dvd h (card_Co3 ▸ Subgroup.card_dvd_of_surjective (f := f) hf)

end TauCeti.Sporadic
