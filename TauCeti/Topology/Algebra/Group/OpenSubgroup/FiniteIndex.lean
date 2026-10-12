/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open subgroups of a compact group are compact and have finite index

Mathlib already knows the coset space of an open subgroup `U` of a compact group `G` to be
finite: `G ⧸ U` is compact and discrete, and that is registered as an instance. The step from
there to `Subgroup.FiniteIndex` is `Subgroup.finiteIndex_of_finite_quotient`, which Mathlib
keeps a theorem rather than an instance — its converse `Subgroup.finite_quotient_of_finiteIndex`
is an instance, so instance search would be free to run the two against each other. The
consequence is that instance search closes `Finite (G ⧸ U.toSubgroup)` on its own but fails on
`U.toSubgroup.FiniteIndex`, so a development that hands an open subgroup of a compact group to
an API stated for `[H.FiniteIndex]` — a sum over cosets, a corestriction — has to supply the
bridge by hand.

This file installs it once. The cycle cannot bite here because the hypothesis is discharged by
the structural `Finite (G ⧸ U.toSubgroup)` instance for a bundled `OpenSubgroup`, not by a
`FiniteIndex` hypothesis. Only separate continuity of multiplication is assumed, matching the
hypotheses of the Mathlib instance being used.

The same bundling supplies the other instance an open subgroup of a compact group needs when it
is handed to an API stated for a compact group, such as the profinite theory of a closed subgroup:
an open subgroup is closed, so it is compact.

## Main results

* `OpenSubgroup.finiteIndex_toSubgroup`: the underlying subgroup of an open subgroup of a
  compact group has finite index.
* `OpenSubgroup.compactSpace_toSubgroup`: the underlying subgroup of an open subgroup of a
  compact group is compact.
-/

public section

/-- **An open subgroup of a compact group has finite index.** Its coset space is compact and
discrete, hence finite. -/
@[to_additive /-- **An open additive subgroup of a compact additive group has finite index.**
Its coset space is compact and discrete, hence finite. -/]
instance OpenSubgroup.finiteIndex_toSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    U.toSubgroup.FiniteIndex :=
  Subgroup.finiteIndex_of_finite_quotient

/-- **An open subgroup of a compact group is compact.** It is closed, being the complement of the
union of its other cosets, and a closed subset of a compact space is compact. -/
@[to_additive /-- **An open additive subgroup of a compact additive group is compact.** It is
closed, being the complement of the union of its other cosets, and a closed subset of a compact
space is compact. -/]
instance OpenSubgroup.compactSpace_toSubgroup {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    CompactSpace U.toSubgroup :=
  isCompact_iff_compactSpace.mp U.isClosed.isCompact
