/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Deck.SubgroupFiberOrbitQuotientGroup

/-!
# Bottom fibre-orbit quotient and quotient-group imports

The bottom-subgroup fibre-orbit equivalence itself lives in `SubgroupFiberOrbit.lean`; the
generic comparison with deck-group quotients lives in `SubgroupFiberOrbitQuotientGroup.lean`.
This module intentionally adds no specialized quotient-group wrappers for `⊥`: those facts
are obtained directly from the generic subgroup-quotient lemmas together with
`QuotientGroup.quotientBot`.
-/

public section

namespace TauCeti

namespace Deck

end Deck

end TauCeti
