/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.IsUniformGroup.Constructions
public import Mathlib.Topology.Algebra.UniformConvergence
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.UniformSpace.CompactConvergence
import TauCeti.Topology.Compactness.Compact

/-!
# Compact convergence is a uniform group structure

For a uniform group `G`, the uniformity of compact convergence on the continuous maps `C(α, G)`
is a uniform group structure for pointwise multiplication. Indeed, it is induced by the
multiplicative embedding of `C(α, G)` into the maps `α → G` with uniform convergence on compact
sets (`ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact`), which form a uniform group.

In particular, continuous homomorphisms of topological groups into `C(α, G)` are uniformly
continuous, so they map Cauchy filters to Cauchy filters; this is how completeness of `C(α, G)`
for compact convergence is used in limits of spaces of maps.

Convergence in the compact-open topology of continuous maps with values in a compact set `K` can
be read through a continuous map that is injective on `K`, when its target is a Hausdorff uniform
space (`IsCompact.tendsto_of_tendstoLocallyUniformly_comp`): it restricts to a closed embedding of
`K`, and locally uniform convergence of the composites gives convergence in `C(T, Y)`.
-/

public section

namespace ContinuousMap

variable {α G : Type*} [TopologicalSpace α] [UniformSpace G] [Group G] [IsUniformGroup G]

/-- The uniformity of compact convergence on `C(α, G)` is a uniform group structure. -/
@[to_additive /-- The uniformity of compact convergence on `C(α, G)` is a uniform additive group
structure. -/]
instance instIsUniformGroup : IsUniformGroup C(α, G) :=
  isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing.isUniformGroup
    (MonoidHom.mk' (toUniformOnFunIsCompact : C(α, G) → _) fun _ _ ↦ rfl)

end ContinuousMap

namespace TauCeti

open Filter Set Topology

/-- **Convergence of maps into a compact set is read through a continuous injection.** Let `f` be
continuous and injective on a compact set `K`, with values in a Hausdorff uniform space, and let
`g i` and `g₀` be continuous maps with values in `K`. If the maps `f ∘ g i` converge locally
uniformly to `f ∘ g₀`, then the maps `g i` converge to `g₀` in the compact-open topology. -/
theorem _root_.IsCompact.tendsto_of_tendstoLocallyUniformly_comp {T X Y ι : Type*}
    [TopologicalSpace T] [TopologicalSpace X] [UniformSpace Y] [T2Space Y] {K : Set X}
    {f : X → Y} (hK : IsCompact K) (hf : ContinuousOn f K) (hinj : InjOn f K) {l : Filter ι}
    {g : ι → C(T, X)} {g₀ : C(T, X)} (hg : ∀ i t, g i t ∈ K) (hg₀ : ∀ t, g₀ t ∈ K)
    (h : TendstoLocallyUniformly (fun i t ↦ f (g i t)) (f ∘ g₀) l) :
    Tendsto g l (𝓝 g₀) := by
  -- As maps into `K`, the `g i` converge, measured by the closed embedding `f` of `K`.
  let k : ι → C(T, K) := fun i ↦ ⟨fun t ↦ ⟨g i t, hg i t⟩, (map_continuous (g i)).codRestrict _⟩
  let k₀ : C(T, K) := ⟨fun t ↦ ⟨g₀ t, hg₀ t⟩, (map_continuous g₀).codRestrict _⟩
  have hemb := hK.isClosedEmbedding_domRestrict hf hinj
  have hk : Tendsto k l (𝓝 k₀) :=
    (ContinuousMap.isEmbedding_postcomp ⟨_, hemb.continuous⟩ hemb.isEmbedding).tendsto_nhds_iff.2
      (ContinuousMap.tendsto_of_tendstoLocallyUniformly h)
  exact ((ContinuousMap.continuous_postcomp ⟨Subtype.val, continuous_subtypeVal⟩).tendsto k₀).comp
    hk

end TauCeti
