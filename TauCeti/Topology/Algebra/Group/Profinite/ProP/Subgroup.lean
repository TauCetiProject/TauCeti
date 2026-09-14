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

Every subgroup of a pro-`p` profinite group is pro-`p` in its subspace topology. Closedness is
not needed for this predicate: it is needed only to make the subgroup itself a profinite group.

The proof compares a finite continuous quotient of the subgroup with its image in a sufficiently
small finite continuous quotient of the ambient group. More generally,
`isProP_iff_isPGroup_map_mk'` characterizes the pro-`p` property of an arbitrary subgroup by
these ambient finite images. This form is useful when a subgroup is constructed as an inverse
limit of prescribed subgroups of the ambient finite quotients.

## Main results

* `isProP_iff_isPGroup_map_mk'`: a subgroup is pro-`p` exactly when all its images in the
  ambient finite continuous quotients are `p`-groups.
* `IsProP.subgroup`: every subgroup of a pro-`p` profinite group is pro-`p`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A subgroup of a profinite group is pro-`p` exactly when its image in every finite continuous
quotient of the ambient group is a `p`-group.

The reverse implication is the cofinality statement: every open normal subgroup of the subgroup
contains the pullback of an ambient open normal subgroup. -/
theorem isProP_iff_isPGroup_map_mk' {P : Subgroup G} :
    IsProP p P ↔
      ∀ U : OpenNormalSubgroup G,
        IsPGroup p (P.map (QuotientGroup.mk' U.toSubgroup)) := by
  constructor
  · exact fun hP U ↦ hP.isPGroup_map_mk' U
  · intro hP
    rw [isProP_iff]
    intro V
    obtain ⟨U, hUV⟩ := Subgroup.exists_openNormalSubgroup_comap_le P V
    let f : P →* G ⧸ U.toSubgroup :=
      (QuotientGroup.mk' U.toSubgroup).domRestrict P
    have hfP : IsPGroup p f.range := by
      dsimp [f]
      rw [MonoidHom.domRestrict_range]
      exact hP U
    let q : P →* P ⧸ V.toSubgroup := QuotientGroup.mk' V.toSubgroup
    have hker : f.ker ≤ q.ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      apply (QuotientGroup.eq_one_iff x).mpr
      apply hUV
      exact (QuotientGroup.eq_one_iff (x : G)).mp hx
    have hker' : f.rangeRestrict.ker ≤ q.ker := by
      rwa [MonoidHom.ker_rangeRestrict]
    let q' : f.range →* P ⧸ V.toSubgroup :=
      f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q, hker'⟩
    apply hfP.of_surjective q'
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup z
    exact ⟨f.rangeRestrict x, by simp [q', q]⟩

/-- Every subgroup of a pro-`p` profinite group is pro-`p` in the subspace topology.

In particular this applies to closed subgroups, which inherit the profinite topology from the
ambient group. -/
theorem IsProP.subgroup (hG : IsProP p G) (P : Subgroup G) : IsProP p P := by
  rw [isProP_iff_isPGroup_map_mk']
  intro U
  exact (isProP_iff.mp hG U).to_subgroup (P.map (QuotientGroup.mk' U.toSubgroup))

end TauCeti
