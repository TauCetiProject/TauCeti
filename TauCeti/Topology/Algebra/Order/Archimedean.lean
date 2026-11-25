/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Compact
public import TauCeti.Algebra.Order.Archimedean.Subgroup

/-!
# Compact subgroups of Archimedean ordered groups

A compact set in an order topology is bounded above, and a bounded-above subgroup of an Archimedean
linearly ordered commutative group is trivial (`Subgroup.eq_bot_of_bddAbove`). So such a group,
for instance `(ℝ, +)`, has no nontrivial compact subgroup.

## Main results

* `Subgroup.eq_bot_of_isCompact` and `AddSubgroup.eq_bot_of_isCompact`: a compact subgroup of an
  Archimedean linearly ordered commutative group is trivial.
-/

public section

namespace Subgroup

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]
  [TopologicalSpace G] [ClosedIciTopology G]

/-- **A compact subgroup of an Archimedean ordered group is trivial**, being bounded above. -/
@[to_additive /-- **A compact additive subgroup of an Archimedean ordered group is trivial**, being
bounded above. For instance, `(ℝ, +)` has no nontrivial compact subgroup. -/]
theorem eq_bot_of_isCompact {H : Subgroup G} (hH : IsCompact (H : Set G)) : H = ⊥ :=
  eq_bot_of_bddAbove hH.bddAbove

end Subgroup
