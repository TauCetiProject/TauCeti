/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Order.Filter.CountablyGenerated
public import TauCeti.Topology.Algebra.Group.CompactOpenSubgroup
public import TauCeti.Topology.Algebra.Group.ContinuousAut.Basic
public import TauCeti.Topology.Algebra.Group.OpenSubgroup.FiniteIndex

/-!
# Continuous automorphisms acting on compact open subgroups

A continuous automorphism `φ` of a topological group `G` carries a compact open subgroup `U` to
the compact open subgroup `φ • U`, its image. This is an action of `ContinuousAut G` on the
refinement index `TauCeti.CompactOpenSubgroup G` by order isomorphisms, and in particular `G`
acts by conjugation, `U ↦ g U g⁻¹`, through `TauCeti.ContinuousAut.conj`. This is a reindexing of
the levels, not an arrow of the index: conjugation by `diag(p, 1)` moves `GL₂(ℤ_p)` to a different
compact open subgroup of `GL₂(ℚ_p)`. Transport by `g` followed by transport by `h` is transport by
`h * g`.

In a first countable nonarchimedean group, such as a `p`-adic Lie group, every compact open `K₀`
contains a descending sequence of compact open subgroups, each normalized by `K₀`, that is a
neighbourhood basis of the identity. Their quotients `K₀ ⧸ U r` are the finite deck groups of a
tower over level `K₀`.

## Main definitions

* The action of `TauCeti.ContinuousAut G` on `TauCeti.CompactOpenSubgroup G` by images, with
  `TauCeti.ContinuousAut.smul_compactOpenSubgroup_toSubgroup` computing the underlying subgroup.

## Main results

* `TauCeti.ContinuousAut.conj_smul_compactOpenSubgroup_toSubgroup`: conjugating a compact open
  subgroup is Mathlib's pointwise conjugation `ConjAct.toConjAct g • U` of the underlying subgroup.
* `TauCeti.CompactOpenSubgroup.exists_le_conj_smul_eq`: every open subgroup contains a compact
  open subgroup of a given compact open `K₀` which is normalized by `K₀`.
* `TauCeti.CompactOpenSubgroup.exists_hasAntitoneBasis_conj_smul_eq`: in a first countable
  nonarchimedean group, every compact open `K₀` contains a descending sequence of compact open
  subgroups normalized by `K₀` that is a neighbourhood basis of the identity.

## References

* M. Emerton, *On the interpolation of systems of eigenvalues attached to automorphic Hecke
  eigenforms*, author draft of 2 January 2006, §2.1 opening, p. 20, and §2.2, pp. 27–28: the
  tower of levels, computing its colimit along a normal compact basis, and the transport of
  levels by the group action.
-/

public section

open Filter Topology
open scoped Pointwise

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace ContinuousAut

/-- A continuous automorphism acts on compact open subgroups by taking images. -/
instance : MulAction (ContinuousAut G) (CompactOpenSubgroup G) where
  smul φ U := φ.compactOpenSubgroupOrderIso U
  -- Each `•` is the `smul` field just given; `change` restates it as transport. Then `φ.symm`
  -- is restated as `φ⁻¹` so that the group lemmas for `1` and `*` apply.
  one_smul U := CompactOpenSubgroup.ext fun x ↦ by
    change x ∈ (1 : ContinuousAut G).compactOpenSubgroupOrderIso U ↔ _
    rw [ContinuousMulEquiv.mem_compactOpenSubgroupOrderIso, ← inv_apply, inv_one, one_apply]
  mul_smul φ ψ U := CompactOpenSubgroup.ext fun x ↦ by
    change x ∈ (φ * ψ).compactOpenSubgroupOrderIso U ↔
      x ∈ φ.compactOpenSubgroupOrderIso (ψ.compactOpenSubgroupOrderIso U)
    simp only [ContinuousMulEquiv.mem_compactOpenSubgroupOrderIso, ← inv_apply, mul_inv_rev,
      mul_apply]

/-- The action of a continuous automorphism on compact open subgroups is transport along it by
`ContinuousMulEquiv.compactOpenSubgroupOrderIso`, so that order isomorphism API applies to it. -/
theorem smul_compactOpenSubgroup_def (φ : ContinuousAut G) (U : CompactOpenSubgroup G) :
    φ • U = φ.compactOpenSubgroupOrderIso U :=
  (rfl)

/-- The underlying subgroup of `φ • U` is the image of `U` under `φ`. -/
@[simp]
theorem smul_compactOpenSubgroup_toSubgroup (φ : ContinuousAut G) (U : CompactOpenSubgroup G) :
    (φ • U).toSubgroup = U.toSubgroup.map φ.toMulEquiv.toMonoidHom :=
  φ.compactOpenSubgroupOrderIso_apply_toSubgroup U

/-- An element lies in `φ • U` exactly when its preimage under `φ` lies in `U`. -/
@[simp]
theorem mem_smul_compactOpenSubgroup_iff {φ : ContinuousAut G} {U : CompactOpenSubgroup G}
    {x : G} : x ∈ φ • U ↔ φ.symm x ∈ U :=
  φ.mem_compactOpenSubgroupOrderIso U

/-- The underlying set of `φ • U` is the image of `U` under `φ`. -/
@[simp, norm_cast]
theorem coe_smul_compactOpenSubgroup (φ : ContinuousAut G) (U : CompactOpenSubgroup G) :
    ((φ • U : CompactOpenSubgroup G) : Set G) = φ '' U :=
  φ.coe_compactOpenSubgroupOrderIso U

/-- Transport by a continuous automorphism preserves and reflects inclusion. -/
@[simp]
theorem smul_compactOpenSubgroup_le_smul_iff {φ : ContinuousAut G}
    {U V : CompactOpenSubgroup G} : φ • U ≤ φ • V ↔ U ≤ V :=
  φ.compactOpenSubgroupOrderIso.le_iff_le

/-- Transport by a continuous automorphism commutes with common refinements. -/
theorem smul_compactOpenSubgroup_inf [SeparatelyContinuousMul G] (φ : ContinuousAut G)
    (U V : CompactOpenSubgroup G) : φ • (U ⊓ V) = φ • U ⊓ φ • V :=
  φ.compactOpenSubgroupOrderIso.map_inf U V

section Conj

variable [SeparatelyContinuousMul G]

/-- An element lies in the conjugate `g U g⁻¹` exactly when its conjugate `g⁻¹ x g` lies
in `U`. -/
theorem mem_conj_smul_compactOpenSubgroup_iff {g x : G} {U : CompactOpenSubgroup G} :
    x ∈ conj g • U ↔ g⁻¹ * x * g ∈ U := by
  rw [mem_smul_compactOpenSubgroup_iff, conj_symm_apply]

/-- Conjugating a compact open subgroup by `g` is Mathlib's pointwise conjugation of the
underlying subgroup by `ConjAct.toConjAct g`. -/
theorem conj_smul_compactOpenSubgroup_toSubgroup (g : G) (U : CompactOpenSubgroup G) :
    (conj g • U).toSubgroup = ConjAct.toConjAct g • U.toSubgroup := by
  ext x
  rw [CompactOpenSubgroup.mem_toSubgroup, mem_conj_smul_compactOpenSubgroup_iff]
  simp [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]

/-- Conjugating a compact open subgroup by an element of the normalizer of its underlying subgroup
does not move it. -/
theorem conj_smul_compactOpenSubgroup_eq_self_of_mem_normalizer {g : G}
    {U : CompactOpenSubgroup G} (hg : g ∈ Subgroup.normalizer (U.toSubgroup : Set G)) :
    conj g • U = U :=
  CompactOpenSubgroup.toSubgroup_injective <| (conj_smul_compactOpenSubgroup_toSubgroup g U).trans
    (Subgroup.conjAct_pointwise_smul_eq_self hg)

/-- Conjugating a compact open subgroup by one of its own elements does not move it. -/
theorem conj_smul_compactOpenSubgroup_eq_self_of_mem {g : G} {U : CompactOpenSubgroup G}
    (hg : g ∈ U) : conj g • U = U :=
  conj_smul_compactOpenSubgroup_eq_self_of_mem_normalizer <|
    Subgroup.le_normalizer (U.mem_toSubgroup.2 hg)

end Conj

end ContinuousAut

namespace CompactOpenSubgroup

/-! ### Normal bases below a level -/

section NormalBasis

/-- **Normal cores below a level.** Every open subgroup `W` contains a compact open subgroup of a
given compact open subgroup `K₀` which is normalized by `K₀`: the normal core in `K₀` of
`W ∩ K₀`. -/
theorem exists_le_conj_smul_eq [SeparatelyContinuousMul G] (K₀ : CompactOpenSubgroup G)
    (W : OpenSubgroup G) :
    ∃ N : CompactOpenSubgroup G, N.toOpenSubgroup ≤ W ∧ N ≤ K₀ ∧
      ∀ k ∈ K₀, ContinuousAut.conj k • N = N := by
  set K := K₀.toSubgroup
  -- An open normal subgroup of `K₀` inside the trace of `W` on `K₀` (its normal core).
  let W' : OpenSubgroup K := W.comap K.subtype continuous_subtypeVal
  obtain ⟨M, hMW, -⟩ := W'.exists_openNormalSubgroup_le
  let C : Subgroup K := M.toSubgroup
  have hCK : C.map K.subtype ≤ K := Subgroup.map_subtype_le C
  let N₀ : OpenSubgroup G := ⟨C.map K.subtype, by
    -- Restate the carrier through the set coercion, which `Subgroup.coe_map` computes as an image.
    change IsOpen (C.map K.subtype : Set G)
    rw [Subgroup.coe_map]
    exact K₀.isOpen.isOpenMap_subtypeVal _ M.isOpen⟩
  let N : CompactOpenSubgroup G := ⟨N₀, K₀.isCompact.of_isClosed_subset N₀.isClosed hCK⟩
  -- The core is normal in `K₀`, so `K₀` normalizes it.
  have hC : ((C.map K.subtype).subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective K.subtype_injective]
    exact M.isNormal'
  refine ⟨N, ?_, (N.toSubgroup_le K₀).1 hCK, fun k hk ↦
    ContinuousAut.conj_smul_compactOpenSubgroup_eq_self_of_mem_normalizer
      (Subgroup.le_normalizer_of_normal_subgroupOf hCK hk)⟩
  rw [← OpenSubgroup.toSubgroup_le]
  exact Subgroup.map_le_iff_le_comap.2 <|
    hMW.trans (OpenSubgroup.toSubgroup_comap W _ _).le

/-- **A descending normal basis below a level.** In a first countable nonarchimedean group, every
compact open subgroup `K₀` contains a descending sequence of compact open subgroups, each
normalized by `K₀`, which is a basis of neighbourhoods of the identity. -/
theorem exists_hasAntitoneBasis_conj_smul_eq [NonarchimedeanGroup G] [FirstCountableTopology G]
    (K₀ : CompactOpenSubgroup G) :
    ∃ U : ℕ → CompactOpenSubgroup G, (𝓝 (1 : G)).HasAntitoneBasis (fun r ↦ (U r : Set G)) ∧
      (∀ r, U r ≤ K₀) ∧ ∀ r, ∀ k ∈ K₀, ContinuousAut.conj k • U r = U r := by
  have hB : (𝓝 (1 : G)).HasBasis
      (fun N : CompactOpenSubgroup G ↦ N ≤ K₀ ∧ ∀ k ∈ K₀, ContinuousAut.conj k • N = N) (↑) := by
    refine ⟨fun s ↦ ⟨fun hs ↦ ?_, fun ⟨N, _, hNs⟩ ↦ mem_of_superset N.mem_nhds_one hNs⟩⟩
    obtain ⟨W, hWs⟩ := NonarchimedeanGroup.is_nonarchimedean s hs
    obtain ⟨N, hNW, hNK, hNc⟩ := K₀.exists_le_conj_smul_eq W
    exact ⟨N, ⟨hNK, hNc⟩, fun x hx ↦ hWs (hNW hx)⟩
  obtain ⟨U, hp, hU⟩ := hB.exists_antitone_subbasis
  exact ⟨U, hU, fun r ↦ (hp r).1, fun r ↦ (hp r).2⟩

end NormalBasis

end CompactOpenSubgroup

end TauCeti
