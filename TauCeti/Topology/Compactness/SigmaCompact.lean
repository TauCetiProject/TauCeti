/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Lindelof

/-!
# Sigma-compact spaces

A Lindelöf space in which every point has a compact neighbourhood is sigma-compact
(`TauCeti.sigmaCompactSpace_of_weaklyLocallyCompactSpace_lindelofSpace`). This generalizes
Mathlib's instance `sigmaCompactSpace_of_locallyCompact_secondCountable`.

A sigma-compact open subset of a locally compact space has a monotone sequence of compact
subsets that exhausts it in the sense that every compact subset lies in one of them
(`IsOpen.exists_monotone_isCompact_subset_forall_isCompact_subset_exists_subset`).
-/

public section

open Set

/-- A weakly locally compact Lindelöf space is sigma-compact: countably many compact
neighbourhoods cover it. This is not an instance, since sigma-compact spaces are Lindelöf. -/
theorem TauCeti.sigmaCompactSpace_of_weaklyLocallyCompactSpace_lindelofSpace {X : Type*}
    [TopologicalSpace X] [WeaklyLocallyCompactSpace X] [LindelofSpace X] :
    SigmaCompactSpace X := by
  choose K hKc hxK using fun x : X ↦ exists_compact_mem_nhds x
  obtain ⟨s, hsc, hsU⟩ := countable_cover_nhds hxK
  refine SigmaCompactSpace.of_countable _ (hsc.image K) (forall_mem_image.2 fun x _ ↦ hKc x) ?_
  rwa [sUnion_image]

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
