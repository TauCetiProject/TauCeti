/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants

/-!
# The norm of a finite group into the invariants

Mathlib's `Representation.norm` is the endomorphism `x ↦ ∑ g, ρ g x` of a representation of a
finite group. Its values are invariant (`Representation.self_norm_apply`), so it factors through
the invariants `ρ.invariants`; this file names that factorization.

## Main definitions

* `Representation.normInvariants`: the norm `V →ₗ[k] ρ.invariants`.

## Main results

* `Representation.coe_normInvariants_apply`: the norm into the invariants is
  `Representation.norm` followed by the inclusion.
-/

public section

namespace Representation

variable {k G V : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- The norm `x ↦ ∑ g, ρ g x` of a representation of a finite group, as a linear map into the
invariants. -/
noncomputable def normInvariants : V →ₗ[k] ρ.invariants :=
  ρ.norm.codRestrict _ fun x ↦ (mem_invariants _ _).mpr fun g ↦ self_norm_apply ρ g x

@[simp]
theorem coe_normInvariants_apply (x : V) : (ρ.normInvariants x : V) = ρ.norm x := (rfl)

end Representation
