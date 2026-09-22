/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Sylow.Existence

/-!
# Sylow pro-`p` subgroups as inverse limits of Sylow subgroups

A Sylow pro-`p` subgroup of a profinite group is the same thing as a compatible choice of Sylow
`p`-subgroup in each of its finite quotients. Such a choice is a `SylowFamily`, a point of the
inverse limit of the finite sets `Sylow p (G ⧸ U)`, and `SylowFamily.equivIsProPSylow` is the
bijection between those points and the Sylow pro-`p` subgroups of `G`.

One direction is `isProPSylow_limitSubgroup`: a compatible family cuts out a Sylow pro-`p`
subgroup. For the other, a Sylow pro-`p` subgroup `P` has a Sylow image `IsProPSylow.toSylow` in
each `G ⧸ U`; those images are compatible along the quotient maps, and `P` is closed, so `P` is
cut out by them. Since a profinite group is the inverse limit of its finite quotients, this says
that the Sylow pro-`p` subgroups of that inverse limit are the inverse limit of the sets of Sylow
subgroups of its levels; existence of a Sylow pro-`p` subgroup (`exists_isProPSylow`) is then
nonemptiness of that inverse limit.

## Main definitions and results

* `SylowFamily`: a compatible family of Sylow `p`-subgroups of the finite quotients, and
  `SylowFamily.subgroup`, the subgroup of `G` it cuts out.
* `IsProPSylow.map_mapOfLE_toSylow`: the finite-quotient images of a Sylow pro-`p` subgroup are
  compatible along the quotient maps.
* `IsProPSylow.limitSubgroup_toSylow`: a Sylow pro-`p` subgroup is cut out by its finite-quotient
  images.
* `SylowFamily.equivIsProPSylow`: the compatible families correspond to the Sylow pro-`p`
  subgroups.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G]

namespace IsProPSylow

variable [Fact p.Prime] [IsTopologicalGroup G] {P : Subgroup G}

/-- The Sylow images of a Sylow pro-`p` subgroup are compatible along the quotient maps
`G ⧸ U →* G ⧸ V`. -/
theorem map_mapOfLE_toSylow (hP : IsProPSylow p P) ⦃U V : OpenNormalSubgroup G⦄ (hUV : U ≤ V) :
    (hP.toSylow U : Subgroup (G ⧸ U.toSubgroup)).map (QuotientGroup.mapOfLE hUV) =
      (hP.toSylow V : Subgroup (G ⧸ V.toSubgroup)) := by
  rw [coe_toSylow, coe_toSylow, Subgroup.map_map, QuotientGroup.mapOfLE_comp_mk']

/-- A Sylow pro-`p` subgroup of a profinite group is cut out by its images in the finite
quotients. -/
theorem limitSubgroup_toSylow [CompactSpace G] [TotallyDisconnectedSpace G]
    (hP : IsProPSylow p P) :
    limitSubgroup (fun U ↦ (hP.toSylow U : Subgroup (G ⧸ U.toSubgroup))) = P := by
  simpa only [coe_toSylow] using limitSubgroup_map_mk' P hP.isClosed

end IsProPSylow

/-- A **Sylow family** of a profinite group `G` at `p`: a Sylow `p`-subgroup of each finite
quotient `G ⧸ U`, compatible along the quotient maps. These are the points of the inverse limit
of the finite sets `Sylow p (G ⧸ U)`, and `SylowFamily.equivIsProPSylow` identifies them with the
Sylow pro-`p` subgroups of `G`. -/
@[ext]
structure SylowFamily (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The Sylow subgroup chosen in the quotient of `G` by the open normal subgroup `U`. -/
  sylow (U : OpenNormalSubgroup G) : Sylow p (G ⧸ U.toSubgroup)
  /-- The chosen Sylow subgroups are compatible along the quotient maps `G ⧸ U →* G ⧸ V`. -/
  map_mapOfLE ⦃U V : OpenNormalSubgroup G⦄ (hUV : U ≤ V) :
    (sylow U : Subgroup (G ⧸ U.toSubgroup)).map (QuotientGroup.mapOfLE hUV) =
      (sylow V : Subgroup (G ⧸ V.toSubgroup))

namespace SylowFamily

/-- The subgroup of `G` cut out by a Sylow family: the elements whose class in each finite
quotient lies in the chosen Sylow subgroup there. -/
def subgroup (S : SylowFamily p G) : Subgroup G :=
  limitSubgroup fun U ↦ (S.sylow U : Subgroup (G ⧸ U.toSubgroup))

/-- An element of `G` lies in the subgroup cut out by a Sylow family exactly when its class in
each finite quotient lies in the chosen Sylow subgroup there. -/
@[simp]
theorem mem_subgroup_iff {S : SylowFamily p G} {g : G} :
    g ∈ S.subgroup ↔ ∀ U : OpenNormalSubgroup G, (g : G ⧸ U.toSubgroup) ∈ S.sylow U :=
  mem_limitSubgroup_iff

variable [IsTopologicalGroup G] [CompactSpace G]

/-- The subgroup cut out by a Sylow family has the chosen Sylow subgroup as its image in each
finite quotient. -/
@[simp]
theorem map_mk'_subgroup (S : SylowFamily p G) (U : OpenNormalSubgroup G) :
    S.subgroup.map (QuotientGroup.mk' U.toSubgroup) =
      (S.sylow U : Subgroup (G ⧸ U.toSubgroup)) :=
  map_mk'_limitSubgroup S.map_mapOfLE U

variable [Fact p.Prime] [TotallyDisconnectedSpace G]

/-- The subgroup cut out by a Sylow family is a Sylow pro-`p` subgroup. -/
theorem isProPSylow_subgroup (S : SylowFamily p G) : IsProPSylow p S.subgroup :=
  isProPSylow_limitSubgroup S.sylow S.map_mapOfLE

/-- **Sylow subgroups of an inverse limit.** The Sylow families of a profinite group `G`
correspond to its Sylow pro-`p` subgroups: a family goes to the subgroup it cuts out, and a
Sylow pro-`p` subgroup to the family of its images in the finite quotients. -/
def equivIsProPSylow : SylowFamily p G ≃ {P : Subgroup G // IsProPSylow p P} where
  toFun S := ⟨S.subgroup, S.isProPSylow_subgroup⟩
  invFun P := ⟨fun U ↦ P.2.toSylow U, fun _ _ hUV ↦ P.2.map_mapOfLE_toSylow hUV⟩
  left_inv S := SylowFamily.ext <| funext fun U ↦
    Sylow.ext <| by rw [IsProPSylow.coe_toSylow, map_mk'_subgroup]
  right_inv P := Subtype.ext P.2.limitSubgroup_toSylow

/-- The correspondence sends a Sylow family to the subgroup it cuts out. -/
@[simp]
theorem equivIsProPSylow_apply_coe (S : SylowFamily p G) :
    (equivIsProPSylow S : Subgroup G) = S.subgroup :=
  (rfl)

/-- The inverse correspondence sends a Sylow pro-`p` subgroup to the family of its images in the
finite quotients. -/
@[simp]
theorem equivIsProPSylow_symm_apply_sylow (P : {P : Subgroup G // IsProPSylow p P})
    (U : OpenNormalSubgroup G) :
    (equivIsProPSylow.symm P).sylow U = P.2.toSylow U :=
  (rfl)

end SylowFamily

end TauCeti
