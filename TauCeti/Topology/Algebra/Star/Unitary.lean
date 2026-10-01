/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# The unitary subgroup of the units is closed

Mathlib's `isClosed_unitary` says that the unitary elements of a topological star monoid `M` are
a closed subset of `M`.  This file transfers that to the group of units: `unitarySubgroup Mˣ`,
the unitary elements of `Mˣ` packaged as a subgroup, is closed in `Mˣ`.

The transfer is immediate once Mathlib's `Units.unitary_eq` exhibits the subgroup as the
preimage of `unitary M` under `Units.val`, which is continuous.  No hypothesis beyond the ones
`isClosed_unitary` already needs is required.

This is the closedness hypothesis that the Lie algebra of a closed subgroup of `Mˣ` is computed
from; see `TauCeti/Geometry/Lie/Subgroup/Unitary.lean`.

## Main results

* `TauCeti.isClosed_unitarySubgroup_units`: the unitary subgroup of `Mˣ` is closed.
-/

public section

namespace TauCeti

variable (M : Type*) [Monoid M] [StarMul M] [TopologicalSpace M] [T1Space M] [ContinuousStar M]
  [ContinuousMul M]

/-- **The unitary subgroup of the units of a topological star monoid is closed.**  It is the
preimage of the closed set `unitary M` under the continuous coercion `Units.val`. -/
theorem isClosed_unitarySubgroup_units :
    IsClosed ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) := by
  have hpre : ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) =
      Units.val ⁻¹' (unitary M : Set M) := by
    rw [show ((unitarySubgroup Mˣ : Subgroup Mˣ) : Set Mˣ) = (unitary Mˣ : Set Mˣ) from rfl,
      Units.unitary_eq]
    rfl
  rw [hpre]
  exact isClosed_unitary.preimage Units.continuous_val

end TauCeti
