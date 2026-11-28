/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible

import Mathlib.Algebra.Group.Commute.Units

/-!
# Rootability of the unit group from roots in the monoid

If every unit of a monoid `M` has an `n`-th root in `M` for each `n ≠ 0`, then that root is
itself a unit, so the unit group `Mˣ` is `ℕ`-rootable. This is the common step behind the
rootability of the units of an algebraically closed field and of an absolutely integrally closed
ring, which supply the roots in `M`.

## Main definitions

* `TauCeti.unitsRootableByNatOfExistsPow`: `RootableBy Mˣ ℕ` from `n`-th roots in `M` of the
  units.
-/

public section

namespace TauCeti

/-- The unit group of a monoid `M` is `ℕ`-rootable as soon as every unit has an `n`-th root in
`M` for each `n ≠ 0`: such a root `z` is a unit, since `z ^ n` is. -/
@[instance_reducible]
noncomputable def unitsRootableByNatOfExistsPow {M : Type*} [Monoid M]
    (h : ∀ n : ℕ, n ≠ 0 → ∀ u : Mˣ, ∃ z : M, z ^ n = u) : RootableBy Mˣ ℕ :=
  rootableByOfPowLeftSurj Mˣ ℕ fun {n} hn u ↦ by
    obtain ⟨z, hz⟩ := h n hn u
    exact ⟨((isUnit_pow_iff hn).mp (hz ▸ u.isUnit)).unit, Units.ext hz⟩

end TauCeti
