/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.LocallyCompact
import TauCeti.Topology.Discrete

/-!
# Topology of open subgroups and their coset spaces

An open subgroup `U : OpenSubgroup G` carries a `Group` structure through `SubgroupClass` and the
subspace topology through `SetLike.coe`, but instance search does not unfold `↥U` to
`↥U.toSubgroup`. Consequently Mathlib's `Subgroup` instances for topological groups do not fire
directly on `U : OpenSubgroup G`, nor does the open-subset theorem `IsOpen.locallyCompactSpace`.

This file registers those instances directly on `OpenSubgroup G` (and `OpenAddSubgroup G`):
separate and joint continuity of multiplication, continuity of inversion, `IsTopologicalGroup`,
`LocallyCompactSpace` (using openness alone), and `WeaklyLocallyCompactSpace` and `CompactSpace`
(using that an open subgroup of a topological group with separately continuous multiplication is
also closed).

The continuity criteria `OpenSubgroup.continuous_mk_inf_iff` and
`OpenSubgroup.continuous_mk_comap_iff` describe maps into coset spaces of intersections and
preimages. These apply to arbitrary open subgroups, without normality. Separate continuity of
multiplication makes the target coset spaces discrete; the preimage criterion only needs this
on the target group of the homomorphism. Both criteria have additive counterparts on
`OpenAddSubgroup`.

## Main instances

* `OpenSubgroup.instSeparatelyContinuousMul`, `OpenSubgroup.instContinuousMul`,
  `OpenSubgroup.instContinuousInv`, `OpenSubgroup.instIsTopologicalGroup`: topological group
  operations on an open subgroup, with additive versions on `OpenAddSubgroup`.
* `OpenSubgroup.instLocallyCompactSpace`, `OpenSubgroup.instWeaklyLocallyCompactSpace`,
  `OpenSubgroup.instCompactSpace`: local compactness and compactness inherited from the ambient
  group, with additive versions on `OpenAddSubgroup`.
-/

public section

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- An open subgroup of a group with separately continuous multiplication has separately
continuous multiplication. -/
@[to_additive /-- An open additive subgroup of an additive group with separately continuous
addition has separately continuous addition. -/]
instance instSeparatelyContinuousMul [SeparatelyContinuousMul G] (U : OpenSubgroup G) :
    SeparatelyContinuousMul U :=
  U.toSubgroup.toSubmonoid.separatelyContinuousMul

/-- An open subgroup of a group with continuous multiplication has continuous multiplication. -/
@[to_additive /-- An open additive subgroup of an additive group with continuous addition has
continuous addition. -/]
instance instContinuousMul [ContinuousMul G] (U : OpenSubgroup G) : ContinuousMul U :=
  U.toSubgroup.toSubmonoid.continuousMul

/-- An open subgroup of a group with continuous inversion has continuous inversion. -/
@[to_additive /-- An open additive subgroup of an additive group with continuous negation has
continuous negation. -/]
instance instContinuousInv [ContinuousInv G] (U : OpenSubgroup G) : ContinuousInv U :=
  ⟨continuous_inv.subtype_map fun _ hx ↦ inv_mem hx⟩

/-- An open subgroup of a topological group is a topological group. -/
@[to_additive /-- An open additive subgroup of a topological additive group is a topological
additive group. -/]
instance instIsTopologicalGroup [IsTopologicalGroup G] (U : OpenSubgroup G) :
    IsTopologicalGroup U where

/-- An open subgroup of a locally compact group is locally compact. -/
@[to_additive /-- An open additive subgroup of a locally compact additive group is locally
compact. -/]
instance instLocallyCompactSpace [LocallyCompactSpace G] (U : OpenSubgroup G) :
    LocallyCompactSpace U :=
  U.isOpen.locallyCompactSpace

/-- An open subgroup of a weakly locally compact group with separately continuous multiplication is
weakly locally compact, since it is closed. -/
@[to_additive /-- An open additive subgroup of a weakly locally compact additive group with
separately continuous addition is weakly locally compact, since it is closed. -/]
instance instWeaklyLocallyCompactSpace [SeparatelyContinuousMul G] [WeaklyLocallyCompactSpace G]
    (U : OpenSubgroup G) : WeaklyLocallyCompactSpace U :=
  U.isClosed.weaklyLocallyCompactSpace

/-- An open subgroup of a compact group with separately continuous multiplication is compact, since
it is closed. -/
@[to_additive /-- An open additive subgroup of a compact additive group with separately continuous
addition is compact, since it is closed. -/]
instance instCompactSpace [SeparatelyContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    CompactSpace U :=
  isCompact_iff_compactSpace.mp U.isClosed.isCompact

variable {H X : Type*} [Group H] [TopologicalSpace H] [TopologicalSpace X]

/-- A map into the coset space of an intersection of open subgroups is continuous if and only
if its projections to both coset spaces are continuous. Normality is not required. -/
@[to_additive /-- A map into the coset space of an intersection of open additive subgroups is
continuous if and only if its projections to both coset spaces are continuous.
Normality is not required. -/]
theorem continuous_mk_inf_iff [SeparatelyContinuousMul G] {U V : OpenSubgroup G} {g : X → G} :
    (Continuous fun x ↦ (g x : G ⧸ (U ⊓ V).toSubgroup)) ↔
      (Continuous fun x ↦ (g x : G ⧸ U.toSubgroup)) ∧
      (Continuous fun x ↦ (g x : G ⧸ V.toSubgroup)) := by
  rw [toSubgroup_inf]
  let φ : G ⧸ (U.toSubgroup ⊓ V.toSubgroup) →
      (G ⧸ U.toSubgroup) × (G ⧸ V.toSubgroup) :=
    fun q ↦ (Subgroup.quotientMapOfLE inf_le_left q, Subgroup.quotientMapOfLE inf_le_right q)
  have hφ (x : G) : φ (QuotientGroup.mk x) =
      ((x : G ⧸ U.toSubgroup), (x : G ⧸ V.toSubgroup)) := by
    simp only [φ, Subgroup.quotientMapOfLE_apply_mk]
  have hcont : Continuous φ :=
    (continuous_id.quotient_map' _).prodMk (continuous_id.quotient_map' _)
  have hinj : Function.Injective φ := by
    refine Quotient.ind₂' ?_
    intro a b h
    simpa only [hφ, Prod.mk.injEq, QuotientGroup.eq, Subgroup.mem_inf] using h
  constructor
  · intro h
    exact ⟨by simpa only [Function.comp_def, hφ] using (hcont.comp h).fst,
      by simpa only [Function.comp_def, hφ] using (hcont.comp h).snd⟩
  · rintro ⟨hU, hV⟩
    apply TauCeti.continuous_of_injective_comp hinj
    simpa only [hφ] using hU.prodMk hV

/-- A map into the coset space of the preimage of an open subgroup is continuous if and only
if its composite with the homomorphism and the target coset projection is continuous.
Normality and continuity of the group operations on the source are not required. -/
@[to_additive /-- A map into the coset space of the preimage of an open additive subgroup is
continuous if and only if its composite with the homomorphism and the target coset projection
is continuous. Normality and continuity of the group operations on the source are not required. -/]
theorem continuous_mk_comap_iff [SeparatelyContinuousMul H] (U : OpenSubgroup H) (f : G →* H)
    (hf : Continuous f) {g : X → G} :
    (Continuous fun x ↦ (g x : G ⧸ (U.comap f hf).toSubgroup)) ↔
      (Continuous fun x ↦ (f (g x) : H ⧸ U.toSubgroup)) := by
  let φ : G ⧸ (U.comap f hf).toSubgroup → H ⧸ U.toSubgroup :=
    Quotient.map' f fun a b h ↦ by
      simpa only [QuotientGroup.leftRel_apply, toSubgroup_comap, Subgroup.mem_comap,
        map_mul, map_inv] using h
  have hφ (x : G) : φ (QuotientGroup.mk x) = (f x : H ⧸ U.toSubgroup) := by
    simp only [φ, Quotient.map'_mk'']
  have hcont : Continuous φ := hf.quotient_map' _
  have hinj : Function.Injective φ := by
    refine Quotient.ind₂' ?_
    intro a b h
    simp only [hφ, QuotientGroup.eq] at h ⊢
    simpa only [toSubgroup_comap, Subgroup.mem_comap, map_mul, map_inv] using h
  constructor
  · intro h
    simpa only [Function.comp_def, hφ] using hcont.comp h
  · intro h
    apply TauCeti.continuous_of_injective_comp hinj
    simpa only [hφ] using h

end OpenSubgroup
