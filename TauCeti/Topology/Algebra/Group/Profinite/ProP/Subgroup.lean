/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Pro-p subgroups

The pro-`p` property passes from a profinite group to each of its subgroups, equipped with the
subspace topology. In particular, a closed subgroup is again a profinite pro-`p` group. The
algebraic property does not itself require closedness: every finite continuous quotient of a
subgroup factors through its image in some finite continuous quotient of the ambient group.

The same factorization characterizes the pro-`p` property of an arbitrary subgroup by its images
in the ambient finite quotients. It also shows that taking the topological closure neither creates
nor destroys the pro-`p` property. This closure form is useful when a subgroup is first generated
algebraically and then promoted to a profinite subgroup.

## Main results

* `Subgroup.isProP_iff_isPGroup_map_quotient`: a subgroup is pro-`p` exactly when all its images
  in the ambient finite continuous quotients are `p`-groups.
* `IsProP.subgroup`: every subgroup of a profinite pro-`p` group is pro-`p` in its subspace
  topology.
* `IsProP.topologicalClosure`, `Subgroup.isProP_topologicalClosure_iff`: the topological closure
  of a pro-`p` subgroup is pro-`p`, and the converse holds as well.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- A subgroup of a profinite group is pro-`p` exactly when its image in every finite
continuous quotient of the ambient group is a `p`-group.

The reverse implication uses that the ambient open normal subgroups induce a neighbourhood basis
on every subgroup. Given an open normal subgroup `V` of `H`, choose an ambient open normal `U`
whose pullback lies in `V`. The quotient `H / V` is then a quotient of the image of `H` in
`G / U`. -/
theorem _root_.Subgroup.isProP_iff_isPGroup_map_quotient (H : Subgroup G) :
    IsProP p H ↔ ∀ U : OpenNormalSubgroup G,
      IsPGroup p (H.map (QuotientGroup.mk' U.toSubgroup)) := by
  constructor
  · exact fun hH U ↦ hH.isPGroup_map_mk' U
  · intro himage
    rw [isProP_iff]
    intro V
    obtain ⟨U, hUV⟩ := H.exists_openNormalSubgroup_comap_le V
    let f : H →* G ⧸ U.toSubgroup :=
      (QuotientGroup.mk' U.toSubgroup).domRestrict H
    have hfP : IsPGroup p f.range := by
      dsimp [f]
      rw [MonoidHom.domRestrict_range]
      exact himage U
    let q : H →* H ⧸ V.toSubgroup := QuotientGroup.mk' V.toSubgroup
    have hker : f.ker ≤ q.ker := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx ⊢
      apply (QuotientGroup.eq_one_iff x).mpr
      apply hUV
      exact (QuotientGroup.eq_one_iff (x : G)).mp hx
    have hker' : f.rangeRestrict.ker ≤ q.ker := by
      rwa [MonoidHom.ker_rangeRestrict]
    let q' : f.range →* H ⧸ V.toSubgroup :=
      f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨q, hker'⟩
    apply hfP.of_surjective q'
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V.toSubgroup z
    exact ⟨f.rangeRestrict x, by simp [q', q]⟩

namespace IsProP

/-- Every subgroup of a profinite pro-`p` group is pro-`p` in its subspace topology.

Closedness is not needed for this property. When `H` is closed, its standard induced instances
also make it a compact totally disconnected topological group. -/
theorem subgroup (hG : IsProP p G) (H : Subgroup G) : IsProP p H := by
  rw [H.isProP_iff_isPGroup_map_quotient]
  exact fun U ↦ ((isProP_iff.mp hG) U).to_subgroup _

/-- The topological closure of a pro-`p` subgroup of a profinite group is pro-`p`. -/
theorem topologicalClosure {H : Subgroup G} (hH : IsProP p H) :
    IsProP p H.topologicalClosure := by
  rw [H.topologicalClosure.isProP_iff_isPGroup_map_quotient]
  intro U
  rw [Subgroup.map_topologicalClosure_quotient_eq]
  exact hH.isPGroup_map_mk' U

end IsProP

/-- Taking the topological closure of a subgroup of a profinite group preserves and reflects the
pro-`p` property. -/
@[simp]
theorem _root_.Subgroup.isProP_topologicalClosure_iff (H : Subgroup G) :
    IsProP p H.topologicalClosure ↔ IsProP p H := by
  constructor
  · intro hH
    rw [H.isProP_iff_isPGroup_map_quotient]
    intro U
    rw [← Subgroup.map_topologicalClosure_quotient_eq]
    exact hH.isPGroup_map_mk' U
  · exact IsProP.topologicalClosure

end TauCeti
