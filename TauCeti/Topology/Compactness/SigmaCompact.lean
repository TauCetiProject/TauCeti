/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.LocallyCompact
public import Mathlib.Topology.Compactness.SigmaCompact

/-!
# Compact exhaustions and local/σ-compactness

Every stage of a `CompactExhaustion` is a compact subspace (`CompactExhaustion.instCompactSpace`),
and any space admitting a `CompactExhaustion` is both weakly locally compact
(`CompactExhaustion.weaklyLocallyCompactSpace`) and σ-compact
(`CompactExhaustion.sigmaCompactSpace`). Conversely, a sigma-compact open subset of a locally
compact space has a monotone sequence of compact subsets that exhausts it in the sense that every
compact subset lies in one of them
(`IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset`).
-/

public section

open Set

namespace CompactExhaustion

variable {X : Type*} [TopologicalSpace X]

/-- Every stage of a `CompactExhaustion` is a compact subspace. -/
instance instCompactSpace (K : CompactExhaustion X) (n : ℕ) : CompactSpace (K n) :=
  isCompact_iff_compactSpace.mp (K.isCompact n)

/-- Any space admitting a `CompactExhaustion` is weakly locally compact. -/
protected theorem weaklyLocallyCompactSpace (K : CompactExhaustion X) :
    WeaklyLocallyCompactSpace X where
  exists_compact_mem_nhds x :=
    let ⟨n, hn⟩ := K.exists_mem_nhds x
    ⟨K n, K.isCompact n, hn⟩

/-- Any space admitting a `CompactExhaustion` is σ-compact. -/
protected theorem sigmaCompactSpace (K : CompactExhaustion X) : SigmaCompactSpace X :=
  ⟨⟨K, K.isCompact, K.iUnion_eq⟩⟩

end CompactExhaustion

/-- A sigma-compact open subset `Ω` of a locally compact space has a monotone sequence of
compact subsets of `Ω` such that every compact subset of `Ω` lies in one of them. -/
theorem IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset
    {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X]
    {Ω : Set X} [SigmaCompactSpace Ω] (hΩ : IsOpen Ω) :
    ∃ L : ℕ → Set X, (∀ m, IsCompact (L m)) ∧ (∀ m, L m ⊆ Ω) ∧ Monotone L ∧
      ∀ K, IsCompact K → K ⊆ Ω → ∃ m, K ⊆ L m := by
  have : LocallyCompactSpace Ω := hΩ.locallyCompactSpace
  let Kx : CompactExhaustion Ω := CompactExhaustion.choice Ω
  refine ⟨fun m => (↑) '' Kx m, fun m => (Kx.isCompact m).image continuous_subtype_val,
    fun m => ?_, fun m m' h => image_mono (Kx.subset h), fun K hK hKΩ => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have hK' : IsCompact (((↑) : Ω → X) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa using hKΩ)
    obtain ⟨m, hm⟩ := Kx.exists_superset_of_isCompact hK'
    exact ⟨m, fun x hx => ⟨⟨x, hKΩ hx⟩, hm hx, rfl⟩⟩
