/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary

/-!
# Unitary units of a star monoid

A star monoid `M` has two unitary groups in play: `unitary M`, the unitary elements of `M`
itself, and `unitary Mˣ`, the unitary elements of the group of units, which Mathlib packages as
the subgroup `unitarySubgroup Mˣ`.  Mathlib relates them by the multiplicative equivalence
`unitarySubgroupUnitsEquiv`; what is missing is the membership statement underlying it, namely
that a unit is unitary exactly when the element of `M` it names is.

That statement is what identifies the unitary subgroup of `Mˣ` as a *preimage*, under the
coercion `Units.val`, of a subset of `M`, and so is what carries topological information about
`unitary M` across to `unitary Mˣ`.

## Main results

* `TauCeti.mem_unitary_units_iff`: a unit of a star monoid is unitary exactly when its underlying
  element is.
-/

public section

namespace TauCeti

variable {M : Type*} [Monoid M] [StarMul M]

/-- **A unit is unitary exactly when the element it names is.**  Both sides say
`star u * u = 1` and `u * star u = 1`; on the left in `Mˣ`, on the right in `M`.  The two are
equivalent because `Units.val` is an injective monoid homomorphism commuting with `star`. -/
theorem mem_unitary_units_iff {u : Mˣ} : u ∈ unitary Mˣ ↔ (u : M) ∈ unitary M := by
  simp only [Unitary.mem_iff]
  exact ⟨fun h => ⟨congr_arg Units.val h.1, congr_arg Units.val h.2⟩,
    fun h => ⟨Units.ext h.1, Units.ext h.2⟩⟩

end TauCeti
