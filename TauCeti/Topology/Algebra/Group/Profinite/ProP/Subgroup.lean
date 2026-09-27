/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.TopologicalAbelianization

/-!
# Subgroups of pro-p groups

The pro-`p` property passes from a profinite group to each of its subgroups. Given an open normal
subgroup `V` of a subgroup `H`, profiniteness supplies an open normal subgroup `N` of the ambient
group whose pullback to `H` lies in `V`. The quotient `H / V` is then a quotient of a subgroup of
the finite `p`-group `G / N`.

Closedness of `H` is not needed for this result. It is needed only when the subgroup itself must
inherit the profinite typeclass stack.

The same factorization characterizes the pro-`p` property of an arbitrary subgroup by its images
in the ambient finite quotients. It also shows that taking the topological closure neither creates
nor destroys the pro-`p` property. This closure form is useful when a subgroup is first generated
algebraically and then promoted to a profinite subgroup.

## Main results

* `Subgroup.isProP_iff_isPGroup_map_mk'`: a subgroup is pro-`p` exactly when all its images
  in the ambient finite continuous quotients are `p`-groups.
* `IsProP.subgroup`, `IsProP.mono`: the pro-`p` property passes to subgroups.
* `IsProP.topologicalAbelianization`: the topological abelianization of a subgroup of a pro-`p`
  group is pro-`p`.
* `IsProP.topologicalClosure`, `Subgroup.isProP_topologicalClosure_iff`: the topological closure
  of a pro-`p` subgroup is pro-`p`, and the converse holds as well.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2.
-/

public section

namespace TauCeti

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A subgroup of a profinite group is pro-`p` exactly when its image in every finite
continuous quotient of the ambient group is a `p`-group. -/
theorem _root_.Subgroup.isProP_iff_isPGroup_map_mk' (H : Subgroup G) :
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

/-- Every subgroup of a pro-`p` profinite group is pro-`p` in the subspace topology.

In particular, a closed subgroup is again a profinite pro-`p` group, since closed subgroups
inherit the remaining profinite instances. -/
theorem subgroup (hG : IsProP p G) (H : Subgroup G) : IsProP p H := by
  exact H.isProP_iff_isPGroup_map_mk'.mpr fun U ↦ (isProP_iff.mp hG U).to_subgroup _

/-- The pro-`p` property is antitone on the subgroups of a profinite group. -/
theorem mono {K H : Subgroup G} (hH : IsProP p H) (hKH : K ≤ H) : IsProP p K := by
  rw [K.isProP_iff_isPGroup_map_mk']
  intro U
  exact (hH.isPGroup_map_mk' U).of_injective
    (Subgroup.inclusion (Subgroup.map_mono hKH)) (Subgroup.inclusion_injective _)

/-- The topological abelianization of a subgroup of a pro-`p` group is pro-`p`. -/
theorem topologicalAbelianization (hG : IsProP p G) (N : Subgroup G) :
    IsProP p (TopologicalAbelianization N) :=
  (hG.subgroup N).quotient _

end IsProP

/-- Taking the topological closure of a subgroup of a profinite group preserves and reflects the
pro-`p` property. -/
@[simp]
theorem _root_.Subgroup.isProP_topologicalClosure_iff (H : Subgroup G) :
    IsProP p H.topologicalClosure ↔ IsProP p H := by
  rw [H.topologicalClosure.isProP_iff_isPGroup_map_mk', H.isProP_iff_isPGroup_map_mk']
  apply forall_congr'
  intro U
  rw [Subgroup.map_topologicalClosure_quotient_eq]

namespace IsProP

/-- The topological closure of a pro-`p` subgroup of a profinite group is pro-`p`. -/
theorem topologicalClosure {H : Subgroup G} (hH : IsProP p H) :
    IsProP p H.topologicalClosure :=
  H.isProP_topologicalClosure_iff.mpr hH

end IsProP

end TauCeti
