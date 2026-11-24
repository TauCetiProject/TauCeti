/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Algebra.NoSmallSubgroups

import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Separation.Connected

/-!
# Topological groups with no small subgroups

A topological group `G` has **no small subgroups** (`TauCeti.HasNoSmallSubgroups G`), or satisfies
the **NSS property** of Gleason–Montgomery–Zippin, when some identity neighbourhood `U ∈ 𝓝 1`
contains no nontrivial subgroup of `G`.

Equivalently, `U` contains no nontrivial cyclic subgroup: an element all of whose integer powers
lie in `U` must equal `1` (`TauCeti.hasNoSmallSubgroups_iff_forall_zpow_mem`). When inversion is
continuous, intersecting `U` with `U⁻¹` reduces this further to natural-number powers
(`TauCeti.hasNoSmallSubgroups_iff_forall_pow_mem`).

The predicate passes to subgroups and pulls back along any injective homomorphism continuous at the
identity (`TauCeti.HasNoSmallSubgroups.of_injective`), is invariant under continuous group
isomorphisms, and is preserved under binary products (`TauCeti.hasNoSmallSubgroups_prod_iff`).
Groups of units `Aˣ` of normed rings with integer norm homogeneity satisfy
`TauCeti.HasNoSmallSubgroups Aˣ` (`TauCeti.hasNoSmallSubgroups_units`), while a profinite group has
no small subgroups if and only if it is discrete
(`TauCeti.hasNoSmallSubgroups_iff_discreteTopology`).

## Main definitions and results

* `TauCeti.HasNoSmallSubgroups`, `TauCeti.HasNoSmallAddSubgroups`: existence of an identity
  neighbourhood containing only the trivial subgroup.
* `TauCeti.hasNoSmallSubgroups_iff_forall_zpow_mem`,
  `TauCeti.hasNoSmallSubgroups_iff_forall_pow_mem`: cyclic power characterizations.
* `TauCeti.HasNoSmallSubgroups.of_injective`, `TauCeti.HasNoSmallSubgroups.subgroup`,
  `ContinuousMulEquiv.hasNoSmallSubgroups_iff`, `TauCeti.hasNoSmallSubgroups_prod_iff`:
  hereditary and invariance properties.
* `TauCeti.hasNoSmallSubgroups_units`, `TauCeti.hasNoSmallAddSubgroups_of_normedAddCommGroup`:
  units of normed rings with integer norm homogeneity have no small subgroups, and normed additive
  groups with integer norm homogeneity have no small additive subgroups.
* `ContinuousMonoidHom.isOpen_ker_of_hasNoSmallSubgroups`,
  `TauCeti.hasNoSmallSubgroups_iff_discreteTopology`: continuous homomorphisms out of profinite
  groups into NSS groups have open kernel, so an NSS profinite group is discrete.

## References

* D. Montgomery and L. Zippin, *Topological Transformation Groups*, Interscience (1955), Chapter II.
* T. Tao, *Hilbert's Fifth Problem and Related Topics*, AMS GSM 153 (2014), §1.2.
-/

public section

open Filter Set
open scoped Topology

namespace TauCeti

section General

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- A topological group `G` has **no small subgroups** when some neighbourhood of `1` contains no
nontrivial subgroup of `G`. -/
@[to_additive HasNoSmallAddSubgroups /-- A topological additive group `G` has **no small additive
subgroups** when some neighbourhood of `0` contains no nontrivial additive subgroup of `G`. -/]
def HasNoSmallSubgroups (G : Type*) [Group G] [TopologicalSpace G] : Prop :=
  ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥

/-- Unfolding characterization of `TauCeti.HasNoSmallSubgroups`. -/
@[to_additive hasNoSmallAddSubgroups_iff]
theorem hasNoSmallSubgroups_iff :
    HasNoSmallSubgroups G ↔ ∃ U ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ U → H = ⊥ :=
  Iff.rfl

/-- A topological group has no small subgroups if and only if there is an identity neighbourhood
`U ∈ 𝓝 1` such that `1` is the only element all of whose integer powers lie in `U`. -/
@[to_additive /-- A topological additive group has no small additive subgroups if and only if there
is a neighbourhood `U ∈ 𝓝 0` such that `0` is the only element all of whose integer multiples lie
in `U`. -/]
theorem hasNoSmallSubgroups_iff_forall_zpow_mem :
    HasNoSmallSubgroups G ↔ ∃ U ∈ 𝓝 (1 : G), ∀ g : G, (∀ n : ℤ, g ^ n ∈ U) → g = 1 := by
  refine ⟨?_, ?_⟩
  · rintro ⟨U, hU, hbot⟩
    refine ⟨U, hU, fun g hg ↦ ?_⟩
    have hsub : ((Subgroup.zpowers g : Subgroup G) : Set G) ⊆ U := by
      rintro _ ⟨n, rfl⟩
      exact hg n
    exact Subgroup.mem_bot.mp (hbot (Subgroup.zpowers g) hsub ▸ Subgroup.mem_zpowers g)
  · rintro ⟨U, hU, hpow⟩
    refine ⟨U, hU, fun H hH ↦ (Subgroup.eq_bot_iff_forall H).mpr fun g hg ↦ ?_⟩
    exact hpow g fun n ↦ hH (H.zpow_mem hg n)

/-- If some neighbourhood `U ∈ 𝓝 1` has the property that `1` is the only element all of whose
natural-number powers lie in `U`, then `G` has no small subgroups. -/
@[to_additive /-- If some neighbourhood `U ∈ 𝓝 0` has the property that `0` is the only element all
of whose natural-number multiples lie in `U`, then `G` has no small additive subgroups. -/]
theorem HasNoSmallSubgroups.of_forall_pow_mem
    (h : ∃ U ∈ 𝓝 (1 : G), ∀ g : G, (∀ n : ℕ, g ^ n ∈ U) → g = 1) :
    HasNoSmallSubgroups G := by
  obtain ⟨U, hU, hpow⟩ := h
  exact hasNoSmallSubgroups_iff_forall_zpow_mem.mpr
    ⟨U, hU, fun g hg ↦ hpow g fun n ↦ by simpa using hg n⟩

/-- When inversion is continuous, having no small subgroups is equivalent to the existence of a
neighbourhood `U ∈ 𝓝 1` such that `1` is the only element all of whose natural-number powers lie in
`U`. -/
@[to_additive /-- When negation is continuous, having no small additive subgroups is equivalent to
the existence of a neighbourhood `U ∈ 𝓝 0` such that `0` is the only element all of whose
natural-number multiples lie in `U`. -/]
theorem hasNoSmallSubgroups_iff_forall_pow_mem [ContinuousInv G] :
    HasNoSmallSubgroups G ↔ ∃ U ∈ 𝓝 (1 : G), ∀ g : G, (∀ n : ℕ, g ^ n ∈ U) → g = 1 := by
  refine ⟨fun hG ↦ ?_, HasNoSmallSubgroups.of_forall_pow_mem⟩
  obtain ⟨U, hU, hzpow⟩ := hasNoSmallSubgroups_iff_forall_zpow_mem.mp hG
  have hUinv : (fun g : G ↦ g⁻¹) ⁻¹' U ∈ 𝓝 (1 : G) :=
    continuous_inv.continuousAt.preimage_mem_nhds (by simpa using hU)
  refine ⟨U ∩ (fun g : G ↦ g⁻¹) ⁻¹' U, inter_mem hU hUinv, fun g hg ↦ hzpow g ?_⟩
  intro n
  cases n with
  | ofNat k => simpa using (hg k).1
  | negSucc k => simpa [zpow_negSucc] using (hg (k + 1)).2

/-- Having no small subgroups pulls back along any injective homomorphism continuous at `1`. -/
@[to_additive /-- Having no small additive subgroups pulls back along any injective additive
homomorphism continuous at `0`. -/]
theorem HasNoSmallSubgroups.of_injective {F : Type*} [FunLike F G G'] [MonoidHomClass F G G']
    (hG' : HasNoSmallSubgroups G') (f : F) (hf_cont : ContinuousAt f 1)
    (hf_inj : Function.Injective f) : HasNoSmallSubgroups G := by
  obtain ⟨U, hU, hpow⟩ := hasNoSmallSubgroups_iff_forall_zpow_mem.mp hG'
  refine hasNoSmallSubgroups_iff_forall_zpow_mem.mpr
    ⟨f ⁻¹' U, hf_cont.preimage_mem_nhds (by simpa [map_one] using hU), fun g hg ↦ ?_⟩
  refine hf_inj ?_
  rw [map_one]
  exact hpow (f g) fun n ↦ by simpa only [mem_preimage, map_zpow] using hg n

/-- Every subgroup of a topological group with no small subgroups has no small subgroups in the
subspace topology. -/
@[to_additive /-- Every additive subgroup of a topological additive group with no small additive
subgroups has no small additive subgroups in the subspace topology. -/]
theorem HasNoSmallSubgroups.subgroup (hG : HasNoSmallSubgroups G) (K : Subgroup G) :
    HasNoSmallSubgroups K :=
  hG.of_injective K.subtype continuous_subtypeVal.continuousAt Subtype.val_injective

/-- Every discrete group has no small subgroups. -/
@[to_additive hasNoSmallAddSubgroups_of_discreteTopology
  /-- Every discrete additive group has no small additive subgroups. -/]
theorem hasNoSmallSubgroups_of_discreteTopology [DiscreteTopology G] : HasNoSmallSubgroups G := by
  refine ⟨{(1 : G)}, isOpen_discrete {(1 : G)} |>.mem_nhds rfl, fun H hH ↦ ?_⟩
  exact (Subgroup.eq_bot_iff_forall H).mpr fun g hg ↦ mem_singleton_iff.mp (hH hg)

/-- Every subsingleton group has no small subgroups. -/
@[to_additive hasNoSmallAddSubgroups_of_subsingleton
  /-- Every subsingleton additive group has no small additive subgroups. -/]
theorem hasNoSmallSubgroups_of_subsingleton [Subsingleton G] : HasNoSmallSubgroups G :=
  ⟨univ, univ_mem, fun H _ ↦ Subsingleton.elim H ⊥⟩

/-- A binary product of topological groups has no small subgroups if and only if both factors do. -/
@[to_additive hasNoSmallAddSubgroups_prod_iff /-- A binary product of topological additive groups
has no small additive subgroups if and only if both factors do. -/]
theorem hasNoSmallSubgroups_prod_iff :
    HasNoSmallSubgroups (G × G') ↔ HasNoSmallSubgroups G ∧ HasNoSmallSubgroups G' := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, ?_⟩
  · exact h.of_injective (ContinuousMonoidHom.inl G G')
      (ContinuousMonoidHom.inl G G').continuous.continuousAt fun _ _ hxy ↦
        congrArg Prod.fst hxy
  · exact h.of_injective (ContinuousMonoidHom.inr G G')
      (ContinuousMonoidHom.inr G G').continuous.continuousAt fun _ _ hxy ↦
        congrArg Prod.snd hxy
  · rintro ⟨hG, hG'⟩
    obtain ⟨U, hU, hUpow⟩ := hasNoSmallSubgroups_iff_forall_zpow_mem.mp hG
    obtain ⟨V, hV, hVpow⟩ := hasNoSmallSubgroups_iff_forall_zpow_mem.mp hG'
    refine hasNoSmallSubgroups_iff_forall_zpow_mem.mpr
      ⟨U ×ˢ V, prod_mem_nhds hU hV, fun x hx ↦ Prod.ext ?_ ?_⟩
    · exact hUpow x.1 fun n ↦ (hx n).1
    · exact hVpow x.2 fun n ↦ (hx n).2

end General

end TauCeti

namespace ContinuousMulEquiv

/-- Having no small subgroups is invariant under continuous multiplicative equivalences. -/
@[to_additive /-- Having no small additive subgroups is invariant under continuous additive
equivalences. -/]
theorem hasNoSmallSubgroups_iff {G G' : Type*} [Group G] [TopologicalSpace G]
    [Group G'] [TopologicalSpace G'] (e : G ≃ₜ* G') :
    TauCeti.HasNoSmallSubgroups G ↔ TauCeti.HasNoSmallSubgroups G' :=
  ⟨fun h ↦ h.of_injective e.symm e.symm.continuous.continuousAt e.symm.injective,
    fun h ↦ h.of_injective e e.continuous.continuousAt e.injective⟩

end ContinuousMulEquiv

namespace ContinuousMonoidHom

variable {G G' : Type*} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']

/-- **A continuous homomorphism into a group with no small subgroups kills every small subgroup.**
There is an identity neighbourhood in the source such that every subgroup contained in it lies in
the kernel. -/
@[to_additive /-- **A continuous additive homomorphism into an additive group with no small additive
subgroups kills every small additive subgroup.** -/]
theorem exists_mem_nhds_one_forall_le_ker_of_hasNoSmallSubgroups
    (f : G →ₜ* G') (hG' : TauCeti.HasNoSmallSubgroups G') :
    ∃ N ∈ 𝓝 (1 : G), ∀ H : Subgroup G, (H : Set G) ⊆ N → H ≤ f.ker := by
  obtain ⟨U, hU, hbot⟩ := hG'
  refine ⟨f ⁻¹' U, f.continuous.continuousAt.preimage_mem_nhds (by simpa using hU),
    fun H hH g hg ↦ ?_⟩
  have hmap : H.map f.toMonoidHom = ⊥ := by
    apply hbot
    rintro _ ⟨x, hx, rfl⟩
    exact hH hx
  exact MonoidHom.mem_ker.mpr
    (Subgroup.mem_bot.mp (hmap ▸ Subgroup.mem_map_of_mem f.toMonoidHom hg))

/-- A continuous homomorphism from a profinite group to a topological group with no small subgroups
has open kernel. -/
@[to_additive /-- A continuous additive homomorphism from a profinite additive group to a
topological additive group with no small additive subgroups has open kernel. -/]
theorem isOpen_ker_of_hasNoSmallSubgroups
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (f : G →ₜ* G') (hG' : TauCeti.HasNoSmallSubgroups G') :
    IsOpen (f.ker : Set G) := by
  obtain ⟨N, hN, hNker⟩ := f.exists_mem_nhds_one_forall_le_ker_of_hasNoSmallSubgroups hG'
  obtain ⟨U, hUN, hU, h1U⟩ := mem_nhds_iff.mp hN
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1U
  exact Subgroup.isOpen_mono (hNker H.toSubgroup (hH.trans hUN)) H.isOpen

end ContinuousMonoidHom

namespace TauCeti

/-- **The units of a normed ring with integer norm homogeneity have no small subgroups.** -/
theorem hasNoSmallSubgroups_units (A : Type*) [NormedRing A] [NormSMulClass ℤ A] :
    HasNoSmallSubgroups Aˣ := by
  obtain ⟨N, hN, hker⟩ := (ContinuousMonoidHom.id Aˣ).exists_mem_nhds_one_forall_le_ker
  refine ⟨N, hN, fun H hH ↦ le_bot_iff.mp ?_⟩
  intro u hu
  exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp (hker H hH hu))

/-- **A normed additive group with integer norm homogeneity has no small additive subgroups.** -/
theorem hasNoSmallAddSubgroups_of_normedAddCommGroup (E : Type*) [NormedAddCommGroup E]
    [NormSMulClass ℤ E] : HasNoSmallAddSubgroups E := by
  refine HasNoSmallAddSubgroups.of_forall_nsmul_mem ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0
    zero_lt_one, fun v hv ↦ ?_⟩
  by_contra hv0
  have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / ‖v‖)
  have hlt : ‖(n : ℤ) • v‖ < 1 := by simpa [natCast_zsmul] using hv n
  rw [norm_smul, Int.norm_natCast] at hlt
  exact hlt.not_ge ((div_lt_iff₀ hpos).mp hn).le

/-- **A profinite group has no small subgroups if and only if it is discrete.** -/
@[to_additive hasNoSmallAddSubgroups_iff_discreteTopology
  /-- **A profinite additive group has no small additive subgroups if and only if it is
discrete.** -/]
theorem hasNoSmallSubgroups_iff_discreteTopology {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    HasNoSmallSubgroups G ↔ DiscreteTopology G := by
  refine ⟨fun hG ↦ discreteTopology_iff_isOpen_singleton_one.mpr ?_,
    fun _ ↦ hasNoSmallSubgroups_of_discreteTopology⟩
  have hopen := (ContinuousMonoidHom.id G).isOpen_ker_of_hasNoSmallSubgroups hG
  have hker : ((ContinuousMonoidHom.id G).ker : Set G) = {(1 : G)} := by
    ext g
    simp [MonoidHom.mem_ker]
  rwa [hker] at hopen

end TauCeti
