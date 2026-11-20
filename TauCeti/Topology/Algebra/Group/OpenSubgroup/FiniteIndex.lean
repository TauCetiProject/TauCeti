/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.GroupTheory.Index.Coatom
import Mathlib.Algebra.Group.Subgroup.Order
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Order.Atoms.Finite

/-!
# Open subgroups of compact groups

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

When multiplication is separately continuous, every proper open subgroup of finite index, in
particular every proper open subgroup of a compact group, lies in a maximal subgroup, which is then
open. The maximal subgroup comes from `Subgroup.exists_isCoatom_le_of_finiteIndex`.

The normal core of an open subgroup of finite index is itself open, so such a subgroup contains an
open normal subgroup of finite index. This needs no compactness.

## Main results

* `OpenSubgroup.finiteIndex_toSubgroup`: the underlying subgroup of an open subgroup of a
  compact group has finite index.
* `OpenSubgroup.compactSpace_toSubgroup`: the underlying subgroup of an open subgroup of a
  compact group is compact.
* `OpenSubgroup.finiteIndex_comap`: the preimage of an open subgroup of finite index under a
  continuous homomorphism has finite index.
* `OpenSubgroup.isOpen_normalCore`: the normal core of an open subgroup of finite index is open.
* `OpenSubgroup.exists_openNormalSubgroup_le`: an open subgroup of finite index
  contains an open normal subgroup of finite index.
* `Subgroup.exists_isOpen_isCoatom_le_of_isOpen`: if multiplication is separately continuous, a
  proper open subgroup of finite index lies in a maximal subgroup, which is open.
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

/-- **The preimage of an open subgroup of finite index has finite index.** Mathlib's instance
for `Subgroup.comap` does not fire on `OpenSubgroup.comap` directly, since instance search does not
unfold it. -/
@[to_additive /-- **The preimage of an open additive subgroup of finite index has finite index.**
Mathlib's instance for `AddSubgroup.comap` does not fire on `OpenAddSubgroup.comap` directly, since
instance search does not unfold it. -/]
instance OpenSubgroup.finiteIndex_comap {G N : Type*} [Group G] [TopologicalSpace G] [Group N]
    [TopologicalSpace N] (U : OpenSubgroup N) [U.toSubgroup.FiniteIndex] (f : G →* N)
    (hf : Continuous f) : (U.comap f hf).toSubgroup.FiniteIndex :=
  inferInstanceAs (U.toSubgroup.comap f).FiniteIndex

section MaximalOpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- **A proper open subgroup of finite index lies in a maximal subgroup, which is open**, when
multiplication is separately continuous. In a compact group every open subgroup has finite index
(`OpenSubgroup.finiteIndex_toSubgroup`), so this applies to every proper open subgroup there. -/
@[to_additive /-- **A proper open additive subgroup of finite index lies in a maximal additive
subgroup, which is open**, when addition is separately continuous. In a compact additive group every
open additive subgroup has finite index (`OpenAddSubgroup.finiteIndex_toAddSubgroup`), so this
applies to every proper open additive subgroup there. -/]
theorem Subgroup.exists_isOpen_isCoatom_le_of_isOpen {K : Subgroup G} [K.FiniteIndex]
    (hKo : IsOpen (K : Set G)) (hK : K ≠ ⊤) :
    ∃ M : Subgroup G, IsOpen (M : Set G) ∧ IsCoatom M ∧ K ≤ M := by
  obtain ⟨M, hM, hKM⟩ := exists_isCoatom_le_of_finiteIndex hK
  exact ⟨M, isOpen_mono hKM hKo, hM, hKM⟩

end MaximalOpenSubgroup

section NormalCore

variable {G : Type*} [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- The normal core of an open subgroup of finite index is open: it is closed, being an
intersection of closed conjugates, and has finite index. -/
@[to_additive /-- The normal core of an open additive subgroup of finite index is open: it is
closed, being an intersection of closed conjugates, and has finite index. -/]
theorem OpenSubgroup.isOpen_normalCore (U : OpenSubgroup G) [U.toSubgroup.FiniteIndex] :
    IsOpen (U.toSubgroup.normalCore : Set G) :=
  Subgroup.isOpen_of_isClosed_of_finiteIndex _ (Subgroup.normalCore_isClosed _ U.isClosed)

/-- An open subgroup of finite index contains an open normal subgroup of finite index, namely its
normal core. -/
@[to_additive /-- An open additive subgroup of finite index contains an open normal additive
subgroup of finite index, namely its normal core. -/]
theorem OpenSubgroup.exists_openNormalSubgroup_le (U : OpenSubgroup G)
    [U.toSubgroup.FiniteIndex] :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup ≤ U.toSubgroup ∧ N.toSubgroup.FiniteIndex :=
  ⟨{ toSubgroup := U.toSubgroup.normalCore, isOpen' := U.isOpen_normalCore },
    Subgroup.normalCore_le _, inferInstance⟩

end NormalCore
