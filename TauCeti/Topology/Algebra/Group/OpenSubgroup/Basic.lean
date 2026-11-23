/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.LocallyConstant.Basic

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
on the target group of the homomorphism.

A compact set meets only finitely many left cosets of an open subgroup
(`IsCompact.finite_image_mk`), since the coset space is discrete.

## Main instances and results

* `OpenSubgroup.instSeparatelyContinuousMul`, `OpenSubgroup.instContinuousMul`,
  `OpenSubgroup.instContinuousInv`, `OpenSubgroup.instIsTopologicalGroup`: topological group
  operations on an open subgroup, with additive versions on `OpenAddSubgroup`.
* `OpenSubgroup.instLocallyCompactSpace`, `OpenSubgroup.instWeaklyLocallyCompactSpace`,
  `OpenSubgroup.instCompactSpace`: local compactness and compactness inherited from the ambient
  group, with additive versions on `OpenAddSubgroup`.
* `OpenSubgroup.directedOn_ge_isCompact_and_le`, `OpenSubgroup.isCoinitial_isCompact_and_le`:
  compact open subgroups below a given open subgroup `U₀` are downward-directed, and when `U₀` is
  compact they form a coinitial family in `OpenSubgroup G`.
* `IsCompact.finite_image_mk`: a compact set meets only finitely many left cosets of an open
  subgroup.
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

/-- For any open subgroup `U₀`, the compact open subgroups contained in `U₀` are downward-directed
(directed under `≥`). -/
@[to_additive /-- For any open additive subgroup `U₀`, the compact open additive subgroups
contained in `U₀` are downward-directed (directed under `≥`). -/]
theorem directedOn_ge_isCompact_and_le [SeparatelyContinuousMul G] (U₀ : OpenSubgroup G) :
    DirectedOn (· ≥ ·) {V : OpenSubgroup G | IsCompact (V : Set G) ∧ V ≤ U₀} :=
  directedOn_of_inf_mem fun V₁ V₂ h₁ _ ↦
    ⟨h₁.1.of_isClosed_subset (V₁ ⊓ V₂).isClosed inf_le_left, inf_le_of_left_le h₁.2⟩

/-- **Cofinality under reverse inclusion.** The compact open subgroups contained in a given compact
open subgroup `U₀` are coinitial in `OpenSubgroup G` (that is, cofinal in `(OpenSubgroup G)ᵒᵈ`
under reverse inclusion `≥`): every open subgroup `W` contains `U₀ ⊓ W`. -/
@[to_additive /-- **Cofinality under reverse inclusion.** The compact open additive subgroups
contained in a given compact open additive subgroup `U₀` are coinitial in `OpenAddSubgroup G` (that
is, cofinal in `(OpenAddSubgroup G)ᵒᵈ` under reverse inclusion `≥`): every open additive subgroup
`W` contains `U₀ ⊓ W`. -/]
theorem isCoinitial_isCompact_and_le [SeparatelyContinuousMul G] {U₀ : OpenSubgroup G}
    (hU₀ : IsCompact (U₀ : Set G)) :
    IsCoinitial {V : OpenSubgroup G | IsCompact (V : Set G) ∧ V ≤ U₀} :=
  fun W ↦ ⟨U₀ ⊓ W, ⟨hU₀.of_isClosed_subset (U₀ ⊓ W).isClosed inf_le_left, inf_le_left⟩,
    inf_le_right⟩

variable {H X : Type*} [Group H] [TopologicalSpace H] [TopologicalSpace X]

/-- A map into the coset space of an intersection of open subgroups is continuous if and only
if its projections to both coset spaces are continuous. Normality is not required. -/
theorem continuous_mk_inf_iff [SeparatelyContinuousMul G] {U V : OpenSubgroup G} {g : X → G} :
    (Continuous fun x ↦ (g x : G ⧸ (U ⊓ V).toSubgroup)) ↔
      (Continuous fun x ↦ (g x : G ⧸ U.toSubgroup)) ∧
      (Continuous fun x ↦ (g x : G ⧸ V.toSubgroup)) := by
  constructor
  · intro h
    have hU : Continuous (Subgroup.quotientMapOfLE
        (inf_le_left : U.toSubgroup ⊓ V.toSubgroup ≤ U.toSubgroup)) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr QuotientGroup.continuous_mk
    have hV : Continuous (Subgroup.quotientMapOfLE
        (inf_le_right : U.toSubgroup ⊓ V.toSubgroup ≤ V.toSubgroup)) :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr QuotientGroup.continuous_mk
    exact ⟨hU.comp h, hV.comp h⟩
  · rintro ⟨hU, hV⟩
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_isOpen_fiber_apply]
    intro x
    have hfiber :
        (fun y ↦ (g y : G ⧸ (U ⊓ V).toSubgroup)) ⁻¹' {(g x : G ⧸ (U ⊓ V).toSubgroup)} =
          (fun y ↦ (g y : G ⧸ U.toSubgroup)) ⁻¹' {(g x : G ⧸ U.toSubgroup)} ∩
          (fun y ↦ (g y : G ⧸ V.toSubgroup)) ⁻¹' {(g x : G ⧸ V.toSubgroup)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, QuotientGroup.eq]
      exact Subgroup.mem_inf
    rw [hfiber]
    exact (hU.isOpen_preimage _ (isOpen_discrete _)).inter
      (hV.isOpen_preimage _ (isOpen_discrete _))

/-- A map into the coset space of the preimage of an open subgroup is continuous if and only
if its composite with the homomorphism and the target coset projection is continuous.
Normality and continuity of the group operations on the source are not required. -/
theorem continuous_mk_comap_iff [SeparatelyContinuousMul H] (U : OpenSubgroup H) (f : G →* H)
    (hf : Continuous f) {g : X → G} :
    (Continuous fun x ↦ (g x : G ⧸ (U.comap f hf).toSubgroup)) ↔
      (Continuous fun x ↦ (f (g x) : H ⧸ U.toSubgroup)) := by
  let φ : G ⧸ (U.comap f hf).toSubgroup → H ⧸ U.toSubgroup :=
    Quotient.map' f fun a b h ↦ by
      simpa only [QuotientGroup.leftRel_apply, toSubgroup_comap, Subgroup.mem_comap,
        map_mul, map_inv] using h
  constructor
  · intro h
    have hφ : Continuous φ :=
      (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp hf)
    exact hφ.comp h
  · intro h
    apply IsLocallyConstant.continuous
    rw [IsLocallyConstant.iff_isOpen_fiber_apply]
    intro x
    have hfiber :
        (fun y ↦ (g y : G ⧸ (U.comap f hf).toSubgroup)) ⁻¹'
          {(g x : G ⧸ (U.comap f hf).toSubgroup)} =
        (fun y ↦ (f (g y) : H ⧸ U.toSubgroup)) ⁻¹' {(f (g x) : H ⧸ U.toSubgroup)} := by
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff, QuotientGroup.eq]
      simp only [toSubgroup_comap, Subgroup.mem_comap, map_mul, map_inv]
    rw [hfiber]
    exact h.isOpen_preimage _ (isOpen_discrete _)

end OpenSubgroup

/-- A compact set meets only finitely many left cosets of an open subgroup. -/
theorem IsCompact.finite_image_mk {G : Type*} [Group G] [TopologicalSpace G]
    [SeparatelyContinuousMul G] {K : Set G} (hK : IsCompact K) (W : OpenSubgroup G) :
    (((↑) : G → G ⧸ (W : Subgroup G)) '' K).Finite := by
  have := QuotientGroup.discreteTopology W.isOpen
  exact (hK.image continuous_quotient_mk').finite_of_discrete
