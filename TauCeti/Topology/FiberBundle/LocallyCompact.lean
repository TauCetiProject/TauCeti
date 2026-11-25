/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.FiberBundle.Basic

/-!
# Local compactness of fibre bundles

A fibre bundle with locally compact base and model fibre has locally compact total space: near
each point, a local trivialization identifies it with an open subset of the locally compact product
of base and fibre. Together with `TauCeti.FiberBundle.secondCountableTopology_totalSpace`, this
allows σ-compactness results for manifolds to apply to finite-dimensional vector bundles,
including normal and cotangent bundles.
-/

public section

open Bundle Filter Topology

namespace TauCeti.FiberBundle

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

end TauCeti.FiberBundle
