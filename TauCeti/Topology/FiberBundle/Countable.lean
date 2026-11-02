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
including normal bundles.
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

end TauCeti.FiberBundle
