/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Second countability and local compactness of fibre bundles

A fibre bundle with second-countable base and model fibre has second-countable total space, and
one with locally compact base and model fibre has locally compact total space. This allows
metrizability and σ-compactness results for manifolds to apply to finite-dimensional vector
bundles, including normal and cotangent bundles. Over a second-countable base, countably many of
the preferred trivializations `trivializationAt` cover the base
(`TauCeti.FiberBundle.exists_iUnion_baseSet_trivializationAt_eq_univ`); this is how
measurability of sections is tested chart by chart.
-/

public section

open Bundle Set TopologicalSpace Filter Topology

namespace TauCeti.FiberBundle

/-- A fibre bundle with second-countable base and model fibre has second-countable total space. -/
instance secondCountableTopology_totalSpace {B F : Type*} {V : B → Type*}
    [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (V b)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
    [SecondCountableTopology B] [SecondCountableTopology F] :
    SecondCountableTopology (TotalSpace F V) := by
  obtain ⟨s, hs, hcover⟩ := isOpen_iUnion_countable
    (fun b => (trivializationAt F V b).baseSet) (fun b => (trivializationAt F V b).open_baseSet)
  have hbase : ⋃ b ∈ s, (trivializationAt F V b).baseSet = univ := by
    rw [hcover]
    exact eq_univ_of_forall fun b => mem_iUnion.mpr ⟨b, mem_baseSet_trivializationAt F V b⟩
  have := hs.to_subtype
  have : ∀ b : s, SecondCountableTopology (trivializationAt F V b.val).source :=
    fun b => (trivializationAt F V b.val).toOpenPartialHomeomorph.secondCountableTopology_source
  apply secondCountableTopology_of_countable_cover
    (fun b : s => (trivializationAt F V b.val).open_source)
  apply eq_univ_of_forall
  intro p
  obtain ⟨b, hb, hpb⟩ := mem_iUnion₂.mp (hbase ▸ mem_univ p.proj)
  exact mem_iUnion.mpr ⟨⟨b, hb⟩, (trivializationAt F V b).mem_source.mpr hpb⟩

/-- A fibre bundle with locally compact base and model fibre has locally compact total space: near
each point it is homeomorphic to an open subset of the locally compact product of base and fibre.
Together with `TauCeti.FiberBundle.secondCountableTopology_totalSpace`, this makes the total space
σ-compact over a second-countable base with a second-countable fibre. -/
instance locallyCompactSpace_totalSpace {B F : Type*} {V : B → Type*}
    [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (V b)]
    [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]
    [LocallyCompactSpace B] [LocallyCompactSpace F] :
    LocallyCompactSpace (TotalSpace F V) := by
  have (v : TotalSpace F V) : (𝓝 v).HasBasis
      (fun s ↦ s ∈ 𝓝 (trivializationAt F V v.proj v) ∧ IsCompact s ∧
        s ⊆ (trivializationAt F V v.proj).target)
      fun s ↦ (trivializationAt F V v.proj).toOpenPartialHomeomorph.symm '' s := by
    rw [← (trivializationAt F V v.proj).toOpenPartialHomeomorph.symm_map_nhds_eq
      (FiberBundle.mem_trivializationAt_proj_source)]
    exact ((compact_basis_nhds _).hasBasis_self_subset
      ((trivializationAt F V v.proj).open_target.mem_nhds
        ((trivializationAt F V v.proj).map_source
          FiberBundle.mem_trivializationAt_proj_source))).map _
  refine .of_hasBasis this ?_
  rintro v s ⟨-, hs, hst⟩
  exact hs.image_of_continuousOn
    ((trivializationAt F V v.proj).toOpenPartialHomeomorph.continuousOn_symm.mono hst)

variable (F : Type*) {B : Type*} (V : B → Type*) [TopologicalSpace B] [TopologicalSpace F]
  [∀ b, TopologicalSpace (V b)] [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] in
/-- Over a nonempty second-countable base, the base sets of countably many preferred
trivializations `trivializationAt F V (p n)` cover the base. -/
theorem exists_iUnion_baseSet_trivializationAt_eq_univ [SecondCountableTopology B] [Nonempty B] :
    ∃ p : ℕ → B, ⋃ n, (trivializationAt F V (p n)).baseSet = univ := by
  obtain ⟨t, ht, htU⟩ := isOpen_iUnion_countable
    (fun b => (trivializationAt F V b).baseSet) (fun b => (trivializationAt F V b).open_baseSet)
  have hU : ⋃ b, (trivializationAt F V b).baseSet = univ :=
    eq_univ_of_forall fun b => mem_iUnion.mpr ⟨b, mem_baseSet_trivializationAt F V b⟩
  rw [hU] at htU
  have hne : t.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty B›
    obtain ⟨y, hy, -⟩ := mem_iUnion₂.1 (htU.symm ▸ mem_univ x : x ∈ ⋃ y ∈ t, _)
    exact ⟨y, hy⟩
  obtain ⟨p, rfl⟩ := ht.exists_eq_range hne
  exact ⟨p, by rwa [biUnion_range] at htU⟩

end TauCeti.FiberBundle
