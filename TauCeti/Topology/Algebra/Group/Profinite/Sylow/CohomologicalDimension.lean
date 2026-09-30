/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.IndexNotDvd
public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Basic

/-!
# The `p`-cohomological dimension of a profinite group is that of a Sylow subgroup

Let `G` be a profinite group, `p` a prime and `P` a Sylow pro-`p` subgroup of `G`. Then
`cd_p G = cd_p P` (Serre, *Galois Cohomology*, I §3.3, Cor. 1 to Prop. 14; NSW (3.3.6)). The two
halves are proved by different arguments.

* `cd_p G ≤ cd_p P`: every open subgroup of `G` containing `P` has index prime to `p`
  (`TauCeti.IsProPSylow.not_dvd_index_of_le`), so restriction from `G` to `P` is injective on the
  cohomology of every discrete `p`-primary torsion `G`-module in every positive degree, and a
  vanishing statement for `P` transfers to `G`.
* `cd_p P ≤ cd_p G`: `P` is closed, and the `p`-cohomological dimension is monotone in a closed
  subgroup by Shapiro's lemma (`TauCeti.cohomologicalDimensionAt_le_of_isClosed`).

In particular all Sylow pro-`p` subgroups of `G` have the same `p`-cohomological dimension, and the
computation of `cd_p` for an arbitrary profinite group reduces to that of a pro-`p` group.

## Main results

* `TauCeti.CohomologicalDimensionLE.of_isProPSylow`: the vanishing predicate `cd_p P ≤ n` for a
  Sylow pro-`p` subgroup `P` implies `cd_p G ≤ n`.
* `TauCeti.IsProPSylow.cohomologicalDimensionAt_le`: `cd_p G ≤ cd_p P` for a Sylow pro-`p`
  subgroup `P` of a profinite group `G`.
* `TauCeti.IsProPSylow.cohomologicalDimensionLE_iff`: the vanishing predicates `cd_p G ≤ n` and
  `cd_p P ≤ n` are equivalent for a Sylow pro-`p` subgroup `P`.
* `TauCeti.IsProPSylow.cohomologicalDimensionAt_eq`: **`cd_p G = cd_p P`** for a Sylow pro-`p`
  subgroup `P` of a profinite group `G`.

## References

* J.-P. Serre, *Galois Cohomology*, Ch. I, §3.3, Cor. 1 to Prop. 14.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (3.3.6).
-/

public section

namespace TauCeti

universe u v

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {P : Subgroup G}

/-- **`cd_p G ≤ cd_p P` for a Sylow pro-`p` subgroup `P`**, as the vanishing predicate: for a
Sylow pro-`p` subgroup `P` of a profinite group `G`, `CohomologicalDimensionLE p P n` implies
`CohomologicalDimensionLE p G n`. -/
theorem CohomologicalDimensionLE.of_isProPSylow (hP : IsProPSylow p P) {n : ℕ}
    (h : CohomologicalDimensionLE.{v} p P n) : CohomologicalDimensionLE.{v} p G n :=
  h.of_isClosed_of_forall_not_dvd_index Fact.out hP.isClosed hP.not_dvd_index_of_le

/-- **`cd_p G ≤ cd_p P` for a Sylow pro-`p` subgroup `P` of a profinite group `G`** (Serre,
*Galois Cohomology*, I §3.3, Cor. 1 to Prop. 14): the `p`-cohomological dimension of `G` is at most
that of any of its Sylow pro-`p` subgroups. -/
theorem IsProPSylow.cohomologicalDimensionAt_le (hP : IsProPSylow p P) :
    cohomologicalDimensionAt.{v} p G ≤ cohomologicalDimensionAt.{v} p P :=
  cohomologicalDimensionAt_le_of_isClosed_of_forall_not_dvd_index Fact.out hP.isClosed
    hP.not_dvd_index_of_le

/-- **`cd_p G = cd_p P` for a Sylow pro-`p` subgroup `P`**, as the vanishing predicate: for a Sylow
pro-`p` subgroup `P` of a profinite group `G`, `CohomologicalDimensionLE p G n` holds if and only if
`CohomologicalDimensionLE p P n` does. -/
theorem IsProPSylow.cohomologicalDimensionLE_iff (hP : IsProPSylow p P) {n : ℕ} :
    CohomologicalDimensionLE.{u} p G n ↔ CohomologicalDimensionLE.{u} p P n :=
  ⟨fun h ↦ h.of_isClosed hP.isClosed, fun h ↦ h.of_isProPSylow hP⟩

/-- **`cd_p G = cd_p P` for a Sylow pro-`p` subgroup `P` of a profinite group `G`** (Serre,
*Galois Cohomology*, I §3.3, Cor. 1 to Prop. 14; NSW (3.3.6)): the `p`-cohomological dimension of a
profinite group is that of any of its Sylow pro-`p` subgroups. -/
theorem IsProPSylow.cohomologicalDimensionAt_eq (hP : IsProPSylow p P) :
    cohomologicalDimensionAt.{u} p G = cohomologicalDimensionAt.{u} p P :=
  le_antisymm hP.cohomologicalDimensionAt_le (cohomologicalDimensionAt_le_of_isClosed hP.isClosed)

end TauCeti
