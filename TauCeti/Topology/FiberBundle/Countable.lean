/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Second countability of fibre bundles

A fibre bundle with second-countable base and model fibre has second-countable total space.
This allows metrizability results for manifolds to apply to finite-dimensional vector bundles,
including normal bundles. Over a second-countable base, countably many of the preferred
trivializations `trivializationAt` cover the base
(`TauCeti.FiberBundle.exists_iUnion_baseSet_trivializationAt_eq_univ`); this is how
measurability of sections is tested chart by chart.
-/

public section

open Bundle Set TopologicalSpace

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
