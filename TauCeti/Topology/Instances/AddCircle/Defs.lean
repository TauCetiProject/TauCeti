/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Order.Interval.Set.Infinite

/-!
# The additive circle is infinite

For a positive period `p` in a densely ordered archimedean group, `AddCircle p` is in bijection
with the half-open interval `[0, p)` (`AddCircle.equivIco`), which is infinite. In particular the
unit circle `UnitAddCircle` is infinite.

## Main results

* `AddCircle.infinite`: `AddCircle p` is infinite, as an instance.
-/

public section

namespace AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  [DenselyOrdered 𝕜] {p : 𝕜} [Fact (0 < p)]

/-- The additive circle of a positive period in a densely ordered archimedean group is infinite,
being in bijection with the interval `[0, p)`. -/
instance infinite : Infinite (AddCircle p) :=
  (equivIco p 0).infinite_iff.2 (Set.Ico_infinite (by simpa using Fact.out)).to_subtype

end AddCircle
