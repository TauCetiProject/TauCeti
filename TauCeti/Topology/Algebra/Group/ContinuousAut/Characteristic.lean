/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.TopologicallyFinitelyGenerated
public import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# Topologically characteristic subgroups

A subgroup of a topological group is **topologically characteristic** if every continuous
automorphism preserves it. This is weaker than Mathlib's `Subgroup.Characteristic`, which tests
all abstract automorphisms. The distinction matters for profinite groups, whose abstract
automorphisms need not be continuous.

The predicate `TauCeti.IsTopCharacteristic G N` is expressed by the image equation
`N.map φ = N`. Its equivalent image and preimage inclusion criteria make it convenient to prove,
and it is stable under arbitrary suprema and infima. A topologically characteristic subgroup is
normal as soon as inner automorphisms are continuous.

In a topologically finitely generated compact group the topologically characteristic open normal
subgroups are cofinal among the open subgroups: an open subgroup has finite index, there are
finitely many open subgroups of that index, and their intersection is preserved by every
continuous automorphism. When the group is moreover totally disconnected, these subgroups form a
neighbourhood basis of the identity. This is what makes the congruence topology on
`ContinuousAut G` behave well for a topologically finitely generated profinite group `G`.

The characterizations and lattice API parallel Mathlib's API for
`Subgroup.Characteristic` in `Mathlib.Algebra.Group.Subgroup.Basic`.

## Main definitions

* `TauCeti.IsTopCharacteristic`: invariance of a subgroup under every continuous automorphism.

## Main results

* `Subgroup.Characteristic.isTopCharacteristic`: every abstractly characteristic subgroup is
  topologically characteristic.
* `TauCeti.IsTopCharacteristic.normal`: a topologically characteristic subgroup is normal when
  inner automorphisms are continuous.
* `TauCeti.IsTopologicallyFinitelyGenerated.exists_isTopCharacteristic_le`: in a topologically
  finitely generated compact group, every open subgroup contains a topologically characteristic
  open normal subgroup.
* `TauCeti.IsTopologicallyFinitelyGenerated.exists_isTopCharacteristic_subset`: in a topologically
  finitely generated profinite group, every neighbourhood of the identity contains a topologically
  characteristic open normal subgroup.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, 2nd ed., §4.4.
-/

public section

namespace TauCeti

universe u

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- A subgroup is **topologically characteristic** if every continuous automorphism maps it onto
itself. This is weaker than `Subgroup.Characteristic`, which quantifies over all abstract
automorphisms. -/
def IsTopCharacteristic (N : Subgroup G) : Prop :=
  ∀ φ : ContinuousAut G, N.map φ.toMulEquiv.toMonoidHom = N

variable {G} {N K : Subgroup G}

/-- A subgroup is topologically characteristic exactly when every continuous automorphism maps
it onto itself. -/
theorem isTopCharacteristic_iff_map_eq :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N.map φ.toMulEquiv.toMonoidHom = N :=
  Iff.rfl

/-- A subgroup is topologically characteristic exactly when it is the preimage of itself under
every continuous automorphism. -/
theorem isTopCharacteristic_iff_comap_eq :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N.comap φ.toMulEquiv.toMonoidHom = N := by
  simp_rw [IsTopCharacteristic, Subgroup.map_equiv_eq_comap_symm']
  exact ⟨fun h φ ↦ h φ.symm, fun h φ ↦ h φ.symm⟩

/-- To prove that a subgroup is topologically characteristic, it suffices to prove that its
preimage under every continuous automorphism is contained in it. -/
theorem isTopCharacteristic_iff_comap_le :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N.comap φ.toMulEquiv.toMonoidHom ≤ N :=
  isTopCharacteristic_iff_comap_eq.trans
    ⟨fun h φ ↦ le_of_eq (h φ), fun h φ ↦
      le_antisymm (h φ) fun g hg ↦
        h φ.symm ((congr_arg (· ∈ N) (φ.symm_apply_apply g)).mpr hg)⟩

/-- To prove that a subgroup is topologically characteristic, it suffices to prove that it is
contained in its preimage under every continuous automorphism. -/
theorem isTopCharacteristic_iff_le_comap :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N ≤ N.comap φ.toMulEquiv.toMonoidHom :=
  isTopCharacteristic_iff_comap_eq.trans
    ⟨fun h φ ↦ ge_of_eq (h φ), fun h φ ↦
      le_antisymm
        (fun g hg ↦ (congr_arg (· ∈ N) (φ.symm_apply_apply g)).mp (h φ.symm hg)) (h φ)⟩

/-- To prove that a subgroup is topologically characteristic, it suffices to prove that every
continuous automorphism maps it into itself. -/
theorem isTopCharacteristic_iff_map_le :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N.map φ.toMulEquiv.toMonoidHom ≤ N := by
  simp_rw [Subgroup.map_equiv_eq_comap_symm']
  exact isTopCharacteristic_iff_comap_le.trans
    ⟨fun h φ ↦ h φ.symm, fun h φ ↦ h φ.symm⟩

/-- To prove that a subgroup is topologically characteristic, it suffices to prove that the image
under every continuous automorphism contains it. -/
theorem isTopCharacteristic_iff_le_map :
    IsTopCharacteristic G N ↔
      ∀ φ : ContinuousAut G, N ≤ N.map φ.toMulEquiv.toMonoidHom := by
  simp_rw [Subgroup.map_equiv_eq_comap_symm']
  exact isTopCharacteristic_iff_le_comap.trans
    ⟨fun h φ ↦ h φ.symm, fun h φ ↦ h φ.symm⟩

/-- Every abstractly characteristic subgroup is topologically characteristic. -/
theorem _root_.Subgroup.Characteristic.isTopCharacteristic (hN : N.Characteristic) :
    IsTopCharacteristic G N :=
  fun φ ↦ Subgroup.characteristic_iff_map_eq.mp hN φ.toMulEquiv

namespace IsTopCharacteristic

/-- The trivial subgroup is topologically characteristic. -/
theorem bot : IsTopCharacteristic G (⊥ : Subgroup G) :=
  isTopCharacteristic_iff_le_map.mpr fun _φ ↦ bot_le

/-- The whole group is topologically characteristic. -/
theorem top : IsTopCharacteristic G (⊤ : Subgroup G) :=
  isTopCharacteristic_iff_map_le.mpr fun _φ ↦ le_top

/-- The supremum of two topologically characteristic subgroups is topologically characteristic. -/
theorem sup (hN : IsTopCharacteristic G N) (hK : IsTopCharacteristic G K) :
    IsTopCharacteristic G (N ⊔ K) := by
  intro φ
  rw [Subgroup.map_sup, hN φ, hK φ]

/-- An arbitrary supremum of topologically characteristic subgroups is topologically
characteristic. -/
theorem iSup {ι : Sort*} {N : ι → Subgroup G} (hN : ∀ i, IsTopCharacteristic G (N i)) :
    IsTopCharacteristic G (⨆ i, N i) := by
  intro φ
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i ↦ hN i φ

/-- The infimum of two topologically characteristic subgroups is topologically characteristic. -/
theorem inf (hN : IsTopCharacteristic G N) (hK : IsTopCharacteristic G K) :
    IsTopCharacteristic G (N ⊓ K) := by
  rw [isTopCharacteristic_iff_comap_eq]
  intro φ
  rw [Subgroup.comap_inf, isTopCharacteristic_iff_comap_eq.mp hN φ,
    isTopCharacteristic_iff_comap_eq.mp hK φ]

/-- An arbitrary infimum of topologically characteristic subgroups is topologically
characteristic. -/
theorem iInf {ι : Sort*} {N : ι → Subgroup G} (hN : ∀ i, IsTopCharacteristic G (N i)) :
    IsTopCharacteristic G (⨅ i, N i) := by
  rw [isTopCharacteristic_iff_comap_eq]
  intro φ
  rw [Subgroup.comap_iInf]
  exact iInf_congr fun i ↦ isTopCharacteristic_iff_comap_eq.mp (hN i) φ

/-- A topologically characteristic subgroup is normal when inner automorphisms are continuous. -/
theorem normal [SeparatelyContinuousMul G] (hN : IsTopCharacteristic G N) : N.Normal where
  conj_mem := by
    intro n hn g
    rw [← hN (ContinuousAut.conj g)]
    rw [← ContinuousAut.conj_apply]
    exact Subgroup.mem_map_of_mem (ContinuousAut.conj g).toMulEquiv.toMonoidHom hn

end IsTopCharacteristic

section Cofinal

variable [IsTopologicalGroup G] [CompactSpace G]

/-- In a topologically finitely generated compact group, every open subgroup `U` contains a
topologically characteristic open normal subgroup: the intersection of the finitely many open
subgroups of the same index as `U`. -/
theorem IsTopologicallyFinitelyGenerated.exists_isTopCharacteristic_le
    (hG : IsTopologicallyFinitelyGenerated G) (U : OpenSubgroup G) :
    ∃ N : OpenNormalSubgroup G, IsTopCharacteristic G N ∧ (N : Subgroup G) ≤ U := by
  have := hG.finite_openSubgroup_index_eq (U : Subgroup G).index
  let K : Subgroup G :=
    ⨅ V : {V : OpenSubgroup G // (V : Subgroup G).index = (U : Subgroup G).index},
      (V.1 : Subgroup G)
  have hKopen : IsOpen (K : Set G) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun V ↦ V.1.isOpen
  have hKchar : IsTopCharacteristic G K := by
    rw [isTopCharacteristic_iff_le_comap]
    intro φ
    rw [Subgroup.comap_iInf]
    refine le_iInf fun V ↦ ?_
    have hV : ((V.1 : Subgroup G).comap φ.toMulEquiv.toMonoidHom).index = (U : Subgroup G).index :=
      (Subgroup.index_comap_of_surjective (V.1 : Subgroup G) (f := φ.toMulEquiv.toMonoidHom)
        φ.toMulEquiv.surjective).trans V.2
    exact iInf_le_of_le ⟨OpenSubgroup.comap φ.toMulEquiv.toMonoidHom φ.continuous V.1, hV⟩ le_rfl
  have := hKchar.normal
  exact ⟨⟨⟨K, hKopen⟩, inferInstance⟩, hKchar, iInf_le_of_le ⟨U, rfl⟩ le_rfl⟩

variable [TotallyDisconnectedSpace G]

/-- In a topologically finitely generated profinite group, every open neighbourhood of the
identity contains a topologically characteristic open normal subgroup. -/
theorem IsTopologicallyFinitelyGenerated.exists_isTopCharacteristic_subset
    (hG : IsTopologicallyFinitelyGenerated G) {U : Set G} (hU : IsOpen U) (h1 : (1 : G) ∈ U) :
    ∃ N : OpenNormalSubgroup G, IsTopCharacteristic G N ∧ (N : Set G) ⊆ U := by
  obtain ⟨V, hVU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hU h1
  obtain ⟨N, hN, hNV⟩ := hG.exists_isTopCharacteristic_le V.toOpenSubgroup
  exact ⟨N, hN, fun g hg ↦ hVU (hNV hg)⟩

/-- In a topologically finitely generated profinite group, the topologically characteristic open
normal subgroups intersect in the trivial subgroup. -/
theorem IsTopologicallyFinitelyGenerated.iInf_isTopCharacteristic_eq_bot
    (hG : IsTopologicallyFinitelyGenerated G) :
    ⨅ N : {N : OpenNormalSubgroup G // IsTopCharacteristic G N}, (N.1 : Subgroup G) = ⊥ := by
  refine eq_bot_iff.mpr fun g hg ↦
    Subgroup.mem_bot.mpr (Subgroup.eq_one_of_mem_iInf_openNormalSubgroup fun U ↦ ?_)
  obtain ⟨N, hN, hle⟩ := hG.exists_isTopCharacteristic_le U.toOpenSubgroup
  exact hle (Subgroup.mem_iInf.mp hg ⟨N, hN⟩)

end Cofinal

end TauCeti
