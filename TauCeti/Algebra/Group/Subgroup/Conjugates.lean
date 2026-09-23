/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Conjugate subgroups

This file packages the set of conjugates of a subgroup.  A conjugate of `H ≤ G` is the image
of `H` under the inner automorphism `MulAut.conj g` for some `g : G`.

## Main definitions

* `TauCeti.conjugateSubgroups`: the set of conjugates of a subgroup.
-/

public section

namespace TauCeti

/-- The set of conjugates of a subgroup by elements of its ambient group. -/
def conjugateSubgroups {G : Type*} [Group G] (H : Subgroup G) : Set (Subgroup G) :=
  Set.range fun g : G ↦ H.map (MulAut.conj g)

/-- Membership in `conjugateSubgroups H` means being obtained from `H` by conjugation. -/
theorem mem_conjugateSubgroups_iff {G : Type*} [Group G] {H H' : Subgroup G} :
    H' ∈ conjugateSubgroups H ↔ ∃ g : G, H.map (MulAut.conj g) = H' :=
  Iff.rfl

end TauCeti
