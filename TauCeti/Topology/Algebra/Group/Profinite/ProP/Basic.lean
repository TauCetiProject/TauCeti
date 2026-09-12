/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.OpenNormalSubgroup

/-!
# Pro-p groups

A topological group is pro-`p` when each of its continuous finite quotients is a `p`-group.
For the unbundled profinite groups used in Tau Ceti, these quotients are represented by the
quotients by open normal subgroups. This file introduces that quotient-form predicate and its
basic covariant API: abstract `p`-groups are pro-`p`, continuous surjective images of pro-`p`
groups are pro-`p`, and hence so are topological quotients. It also records invariance under
topological group isomorphism and agreement with `IsPGroup` for a discrete topology.

Closedness of a normal subgroup is not needed for the predicate to descend to its quotient.
It is needed only when one wants the quotient of a profinite group to be profinite again; that
separate topological fact is supplied by `QuotientGroup.instTotallyDisconnectedSpace`.

## Main results

* `IsProP`: every quotient by an open normal subgroup is a `p`-group.
* `isProP_iff`: the defining property, as a lemma usable outside this module.
* `IsPGroup.isProP`: an abstract `p`-group with any topology is pro-`p`.
* `isProP_iff_isPGroup`: for a discrete topology, pro-`p` agrees with `IsPGroup`.
* `IsProP.of_surjective`: a continuous surjective image of a pro-`p` group is pro-`p`.
* `IsProP.quotient`: a quotient of a pro-`p` group by a normal subgroup is pro-`p`.
* `IsProP.top`: the top subgroup of a pro-`p` group is pro-`p`.
* `IsProP.isPGroup_range`: a continuous homomorphism from a pro-`p` group to a discrete group
  has a `p`-group as its range.
* `IsProP.isPGroup_map_mk'`: the image of a pro-`p` subgroup in the quotient by an open normal
  subgroup is a `p`-group.
* `isProP_congr`: the predicate is invariant under topological group isomorphism.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.2.
-/

public section

namespace TauCeti

universe u v

/-- A topological group is **pro-`p`** when every quotient by an open normal subgroup is a
`p`-group. For a profinite group these are exactly its continuous finite quotients. -/
def IsProP (p : ℕ) (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup)

variable {p : ℕ}

/-- The defining property of `IsProP`, available to modules that only see the declaration and
not its body. -/
theorem isProP_iff {G : Type u} [Group G] [TopologicalSpace G] :
    IsProP p G ↔ ∀ U : OpenNormalSubgroup G, IsPGroup p (G ⧸ U.toSubgroup) :=
  Iff.rfl

namespace IsPGroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- An abstract `p`-group is pro-`p` for any topology: all of its group quotients are
`p`-groups. -/
theorem _root_.IsPGroup.isProP (hG : IsPGroup p G) : IsProP p G :=
  fun U ↦ hG.to_quotient U.toSubgroup

end IsPGroup

section Discrete

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

/-- On a group with the discrete topology, being pro-`p` is equivalent to being a `p`-group. -/
@[simp]
theorem isProP_iff_isPGroup : IsProP p G ↔ IsPGroup p G := by
  refine ⟨fun hG ↦ ?_, IsPGroup.isProP⟩
  -- The trivial open normal subgroup is `⊥` only through its characterization lemma, so
  -- reach `G ⧸ ⊥` by rewriting the subgroup rather than by definitional unfolding.
  exact (hG (openNormalSubgroupBot G)).of_equiv
    ((QuotientGroup.quotientMulEquivOfEq (openNormalSubgroupBot_toSubgroup G)).trans
      QuotientGroup.quotientBot)

end Discrete

namespace IsProP

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- A continuous surjective image of a pro-`p` group is pro-`p`. -/
theorem of_surjective (hG : IsProP p G) (f : G →* H) (hf : Continuous f)
    (hsurj : Function.Surjective f) : IsProP p H := by
  intro U
  let V := OpenNormalSubgroup.comap U f hf
  let _ : V.toSubgroup.Normal := V.isNormal'
  have hVU : V.toSubgroup ≤ U.toSubgroup.comap f := by simp [V]
  let q : G ⧸ V.toSubgroup →* H ⧸ U.toSubgroup :=
    QuotientGroup.map V.toSubgroup U.toSubgroup f hVU
  apply (hG V).of_surjective q
  exact QuotientGroup.map_surjective_of_surjective V.toSubgroup U.toSubgroup f
    ((QuotientGroup.mk'_surjective U.toSubgroup).comp hsurj) hVU

/-- A quotient of a pro-`p` group by a normal subgroup is pro-`p`.

No closedness hypothesis is needed here: closedness controls whether the quotient topology is
Hausdorff and profinite, not whether its open-normal quotients are `p`-groups. -/
theorem quotient (hG : IsProP p G) (N : Subgroup G) [N.Normal] : IsProP p (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) QuotientGroup.continuous_mk
    (QuotientGroup.mk'_surjective N)

/-- The top subgroup of a pro-`p` group, with its subspace topology, is pro-`p`. -/
theorem top (hG : IsProP p G) : IsProP p (⊤ : Subgroup G) :=
  hG.of_surjective (Subgroup.topEquiv (G := G)).symm.toMonoidHom
    (continuous_induced_rng.mpr continuous_id) (Subgroup.topEquiv (G := G)).symm.surjective

/-- A topological group isomorphism carries the pro-`p` property to its target. -/
theorem of_equiv (hG : IsProP p G) (e : G ≃ₜ* H) : IsProP p H :=
  hG.of_surjective e.toMulEquiv.toMonoidHom e.continuous e.surjective

/-- The range of a continuous homomorphism from a pro-`p` group to a discrete group is a
`p`-group. -/
theorem isPGroup_range [DiscreteTopology H] (hG : IsProP p G) (f : G →* H)
    (hf : Continuous f) : IsPGroup p f.range :=
  isProP_iff_isPGroup.mp <| hG.of_surjective (H := f.range) f.rangeRestrict
    (continuous_induced_rng.mpr hf) f.rangeRestrict_surjective

/-- The image of a pro-`p` subgroup in the quotient by an open normal subgroup is a
`p`-group. -/
theorem isPGroup_map_mk' [IsTopologicalGroup G] {P : Subgroup G} (hP : IsProP p P)
    (U : OpenNormalSubgroup G) : IsPGroup p (P.map (QuotientGroup.mk' U.toSubgroup)) := by
  rw [← MonoidHom.domRestrict_range]
  exact hP.isPGroup_range _ (QuotientGroup.continuous_mk.comp continuous_subtype_val)

end IsProP

/-- Being pro-`p` is invariant under topological group isomorphism. -/
theorem isProP_congr {G : Type u} {H : Type v} [Group G] [TopologicalSpace G]
    [Group H] [TopologicalSpace H] (e : G ≃ₜ* H) : IsProP p G ↔ IsProP p H :=
  ⟨fun hG ↦ hG.of_equiv e, fun hH ↦ hH.of_equiv e.symm⟩

end TauCeti
