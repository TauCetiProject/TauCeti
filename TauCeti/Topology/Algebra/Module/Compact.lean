/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ClopenNhdofOne
public import Mathlib.LinearAlgebra.Quotient.Basic
public import TauCeti.Topology.Algebra.Module.LinearTopology

/-!
# Compact totally disconnected modules over a compact ring

Let `R` be a compact topological ring, or more generally a ring with a compact topology, and let
`M` be an `R`-module that is a compact, totally disconnected topological additive group on which
`R` acts continuously. The standard example is a compact module over the Iwasawa algebra
`ℤ_p[[Γ]]` of a profinite group `Γ`, which is how such modules arise in the study of relation
modules of pro-`p` groups.

The main result is that the topology of `M` is **`R`-linear**
(`TauCeti.isLinearTopology_of_compactSpace`): the open submodules form a basis of neighbourhoods
of `0`. A totally disconnected compact group has a basis of open subgroups at `0`; for an open
subgroup `V`, the elements `m` with `r • m ∈ V` for every `r : R` form a submodule inside `V`,
and it is open because the compactness of `R` makes `r • m` uniformly small in `r` for `m` near
`0` (the tube lemma).

A linearly topologized T1 module is separated by its open submodules
(`TauCeti.eq_zero_of_forall_isOpen_submodule_mem`), and a compact one is the inverse limit of its
quotients by open submodules: a family of classes in the quotients `M ⧸ N`, compatible along the
maps `Submodule.factor`, comes from a unique element of `M` (`TauCeti.existsUnique_forall_mkQ_eq`).
The transition maps `Submodule.factor` of that system are surjective by
`Submodule.factor_surjective`. Levelwise surjections between towers of compact modules induce a
surjection on inverse limits, which is the topological statement
`TauCeti.exists_forall_map_succ_eq_and_forall_eq_of_compact_t2`.

## Main results

* `TauCeti.isLinearTopology_of_compactSpace`: a compact totally disconnected topological module
  over a compact ring is linearly topologized.
* `TauCeti.eq_zero_of_forall_isOpen_submodule_mem`: in a linearly topologized T1 module, an
  element lying in every open submodule is `0`.
* `TauCeti.existsUnique_forall_mkQ_eq`: a compact linearly topologized T1 module is the inverse
  limit of its quotients by open submodules.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 5.1 (profinite modules over profinite
  rings) and Proposition 1.1.4 (the compactness argument behind the limit description).
* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), §4, where compact
  modules over `ℤ_p[[Γ]]` carry the classification.
-/

public section

open Filter Topology

namespace TauCeti

section LinearTopology

variable (R M : Type*) [Ring R] [TopologicalSpace R] [CompactSpace R]
  [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul R M] [CompactSpace M] [TotallyDisconnectedSpace M]

/-- **Compact totally disconnected modules over a compact ring are linearly topologized.** If `M`
is a compact, totally disconnected topological additive group with a continuous action of a ring
`R` carrying a compact topology, then the open `R`-submodules of `M` form a basis of
neighbourhoods of `0`. -/
instance (priority := 100) isLinearTopology_of_compactSpace : IsLinearTopology R M := by
  refine (isLinearTopology_iff_hasBasis_open_submodule (R := R)).2
    ⟨fun U ↦ ⟨fun hU ↦ ?_, fun ⟨N, hN, hNU⟩ ↦ mem_of_superset (hN.mem_nhds N.zero_mem) hNU⟩⟩
  -- An open subgroup `V ⊆ U`, and the submodule of the `m` with `R • m ⊆ V`.
  obtain ⟨V₀, hVU⟩ := ProfiniteGrp.exist_openNormalAddSubgroup_sub_open_nhds_of_zero
    isOpen_interior (mem_interior_iff_mem_nhds.mpr hU)
  let V : AddSubgroup M := V₀.toAddSubgroup
  have hVo : IsOpen (V : Set M) := V₀.isOpen'
  -- `V` is `V₀` with its bundled openness forgotten; the two have the same carrier.
  have hVU' : (V : Set M) ⊆ interior U := hVU
  let N : Submodule R M :=
    { carrier := {m | ∀ r : R, r • m ∈ V}
      add_mem' := fun ha hb r ↦ by simpa only [smul_add] using V.add_mem (ha r) (hb r)
      zero_mem' := fun r ↦ by simpa only [smul_zero] using V.zero_mem
      smul_mem' := fun c m hm r ↦ by simpa only [smul_smul] using hm (r * c) }
  -- The tube lemma: since `R` is compact and `r • 0 = 0 ∈ V` for every `r`, the condition
  -- `∀ r, r • m ∈ V` holds for all `m` near `0`.
  have hN : (N : Set M) ∈ 𝓝 0 := by
    have hV : ∀ r ∈ (Set.univ : Set R),
        ∀ᶠ z : M × R in 𝓝 ((0 : M), r), z.2 • z.1 ∈ (V : Set M) := fun r _ ↦ by
      have hcont : Continuous fun z : M × R ↦ z.2 • z.1 := continuous_snd.smul continuous_fst
      refine hcont.continuousAt.preimage_mem_nhds ?_
      simpa only [smul_zero] using hVo.mem_nhds V.zero_mem
    filter_upwards [isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun m r ↦ r • m ∈ (V : Set M)) hV] with m hm r
    exact hm r (Set.mem_univ r)
  refine ⟨N, N.toAddSubgroup.isOpen_of_mem_nhds hN, fun m hm ↦ ?_⟩
  exact interior_subset (hVU' (SetLike.mem_coe.mpr (by simpa only [one_smul] using hm 1)))

end LinearTopology

section Limit

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsLinearTopology R M]

/-- **A compact linearly topologized module is the inverse limit of its quotients by open
submodules.** In a compact T1 module whose topology is `R`-linear, a family of classes
`x N ∈ M ⧸ N`, one for each open submodule `N`, compatible along the maps
`Submodule.factor : M ⧸ N' → M ⧸ N` for `N' ≤ N`, is the family of classes of a unique element
of `M`. -/
theorem existsUnique_forall_mkQ_eq [IsTopologicalAddGroup M] [CompactSpace M] [T1Space M]
    (x : ∀ N : {N : Submodule R M // IsOpen (N : Set M)}, M ⧸ N.1)
    (hx : ∀ (N N' : {N : Submodule R M // IsOpen (N : Set M)}) (h : N'.1 ≤ N.1),
      Submodule.factor h (x N') = x N) :
    ∃! m : M, ∀ N, N.1.mkQ m = x N := by
  -- The fibres of `M → M ⧸ N` over `x N` are cosets of open, hence closed, submodules; they are
  -- directed by compatibility, so compactness gives a common point.
  let C (N : {N : Submodule R M // IsOpen (N : Set M)}) : Set M := N.1.mkQ ⁻¹' {x N}
  have hne (N : {N : Submodule R M // IsOpen (N : Set M)}) : (C N).Nonempty :=
    N.1.mkQ_surjective (x N)
  have hcl (N : {N : Submodule R M // IsOpen (N : Set M)}) : IsClosed (C N) := by
    obtain ⟨m₀, hm₀⟩ := hne N
    have hC : C N = (· - m₀) ⁻¹' (N.1 : Set M) := by
      ext m
      simp only [C, Set.mem_preimage, Set.mem_singleton_iff] at hm₀ ⊢
      rw [← hm₀, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, SetLike.mem_coe]
    rw [hC]
    exact (N.1.toAddSubgroup.isClosed_of_isOpen N.2).preimage (continuous_sub_right m₀)
  have hdir : Directed (· ⊇ ·) C := fun N N' ↦ by
    refine ⟨⟨N.1 ⊓ N'.1, N.2.inter N'.2⟩, fun m hm ↦ ?_, fun m hm ↦ ?_⟩ <;>
    simp only [C, Set.mem_preimage, Set.mem_singleton_iff] at hm ⊢
    · rw [← hx N ⟨_, N.2.inter N'.2⟩ inf_le_left, ← hm, Submodule.factor_mk]
    · rw [← hx N' ⟨_, N.2.inter N'.2⟩ inf_le_right, ← hm, Submodule.factor_mk]
  have : Nonempty {N : Submodule R M // IsOpen (N : Set M)} := ⟨⟨⊤, isOpen_univ⟩⟩
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hdir hne
    (fun N ↦ (hcl N).isCompact) hcl
  refine ⟨m, fun N ↦ Set.mem_iInter.mp hm N, fun m' hm' ↦ ?_⟩
  -- Uniqueness: `m' - m` lies in every open submodule.
  refine (sub_eq_zero.mp (eq_zero_of_forall_isOpen_submodule_mem R fun N hN ↦ ?_))
  rw [← Submodule.Quotient.eq]
  exact (hm' ⟨N, hN⟩).trans (Set.mem_iInter.mp hm ⟨N, hN⟩).symm

end Limit

end TauCeti
