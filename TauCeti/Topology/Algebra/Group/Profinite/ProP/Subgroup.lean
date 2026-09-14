/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Subgroups of pro-p groups

The pro-`p` property passes from a profinite group to each of its subgroups. Given an open normal
subgroup `V` of a subgroup `H`, profiniteness supplies an open normal subgroup `N` of the ambient
group whose pullback to `H` lies in `V`. The quotient `H / V` is then a quotient of a subgroup of
the finite `p`-group `G / N`.

Closedness of `H` is not needed for this result. It is needed only when the subgroup itself must
inherit the profinite typeclass stack.

## Main result

* `IsProP.subgroup`: every subgroup of a pro-`p` profinite group is pro-`p` in the subspace
  topology.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2.
-/

public section

namespace TauCeti

namespace IsProP

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Every subgroup of a pro-`p` profinite group is pro-`p` in the subspace topology.

In particular, a closed subgroup is again a profinite pro-`p` group, since closed subgroups
inherit the remaining profinite instances. -/
theorem subgroup (hG : IsProP p G) (H : Subgroup G) : IsProP p H := by
  rw [isProP_iff]
  intro V
  obtain ⟨N, hNV⟩ := H.exists_openNormalSubgroup_comap_le V
  intro x
  obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup x
  obtain ⟨k, hk⟩ :=
    isProP_iff.mp hG N (QuotientGroup.mk' N.toSubgroup (h : G))
  refine ⟨k, ?_⟩
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  apply hNV
  rw [Subgroup.mem_comap]
  apply (QuotientGroup.eq_one_iff ((h : G) ^ p ^ k)).mp
  simpa using hk

end IsProP

end TauCeti
