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

section IsUniformGroup

variable {α G : Type*} [TopologicalSpace α] [UniformSpace G] [Group G] [IsUniformGroup G]

/-- The uniformity of compact convergence on `C(α, G)` is a uniform group structure. -/
@[to_additive /-- The uniformity of compact convergence on `C(α, G)` is a uniform additive group
structure. -/]
instance instIsUniformGroup : IsUniformGroup C(α, G) :=
  isUniformEmbedding_toUniformOnFunIsCompact.isUniformInducing.isUniformGroup
    (MonoidHom.mk' (toUniformOnFunIsCompact : C(α, G) → _) fun _ _ ↦ rfl)

end IsUniformGroup

section Postcomp

open Filter Topology

/-- If continuous maps `u i → v` in the compact-open topology on `C(X, M)` along a filter `l`,
and `g : M → Y` is continuous on an open set `V` containing `v '' C'` for a compact set `C'`, then
`g ∘ u i → g ∘ v` uniformly on `C'` along `l`. -/
theorem tendstoUniformlyOn_comp_of_tendsto {X M Y ι : Type*}
    [TopologicalSpace X] [TopologicalSpace M] [UniformSpace Y]
    {l : Filter ι} {u : ι → C(X, M)} {v : C(X, M)} (hlim : Tendsto u l (𝓝 v))
    {V : Set M} (hV : IsOpen V) {g : M → Y} (hg : ContinuousOn g V)
    {C' : Set X} (hC' : IsCompact C') (hvV : Set.MapsTo v C' V) :
    TendstoUniformlyOn (fun i ↦ g ∘ u i) (g ∘ v) l C' := by
  classical
  have : CompactSpace C' := isCompact_iff_compactSpace.1 hC'
  have hev : ∀ᶠ i in l, Set.MapsTo (u i) C' V :=
    (tendsto_nhds_compactOpen.1 hlim) C' hC' V hV hvV
  let incl : C(C', X) := ⟨Subtype.val, continuous_subtypeVal⟩
  let valV : C(V, M) := ⟨Subtype.val, continuous_subtypeVal⟩
  let vV : C(C', V) := ⟨fun x ↦ ⟨v x.val, hvV x.property⟩,
    (v.continuous.comp continuous_subtypeVal).subtype_mk fun x ↦ hvV x.property⟩
  let uV : ι → C(C', V) := fun i ↦
    if h : Set.MapsTo (u i) C' V then
      ⟨fun x ↦ ⟨u i x.val, h x.property⟩,
        ((u i).continuous.comp continuous_subtypeVal).subtype_mk fun x ↦ h x.property⟩
    else vV
  have hlim_C : Tendsto (fun i ↦ (u i).comp incl) l (𝓝 (v.comp incl)) :=
    (continuous_precomp incl).continuousAt.tendsto.comp hlim
  have hlim_V : Tendsto uV l (𝓝 vV) := by
    refine (isInducing_postcomp valV IsInducing.subtypeVal).tendsto_nhds_iff.2 ?_
    refine hlim_C.congr' ?_
    filter_upwards [hev] with i hi
    ext x
    simp [uV, hi, incl, valV]
  let gV : C(V, Y) := ⟨V.domRestrict g, continuousOn_iff_continuous_domRestrict.1 hg⟩
  have hlim_Y : Tendsto (fun i ↦ gV.comp (uV i)) l (𝓝 (gV.comp vV)) :=
    (continuous_postcomp gV).continuousAt.tendsto.comp hlim_V
  have hunif : TendstoUniformly (fun i (x : C') ↦ gV (uV i x)) (fun x : C' ↦ gV (vV x)) l :=
    tendsto_iff_tendstoUniformly.1 hlim_Y
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  intro s hs
  filter_upwards [hunif s hs, hev] with i hi hmap x
  have h1 := hi x
  simp only [uV, dite_eq_left hmap, gV, vV, ContinuousMap.coe_mk, Set.domRestrict_apply] at h1
  exact h1

/-- Variant of `ContinuousMap.tendstoUniformlyOn_comp_of_tendsto` for functions `u i, v : X → M`
that are continuous on `U₀` and converge in `C(U₀, M)`. -/
theorem tendstoUniformlyOn_comp_of_tendsto_domRestrict {X M Y ι : Type*}
    [TopologicalSpace X] [TopologicalSpace M] [UniformSpace Y]
    {l : Filter ι} {U₀ : Set X} {u : ι → X → M} {v : X → M}
    (hu : ∀ i, ContinuousOn (u i) U₀) (hv : ContinuousOn v U₀)
    (hlim : Tendsto (fun i ↦ (⟨U₀.domRestrict (u i), (hu i).domRestrict⟩ : C(U₀, M))) l
      (𝓝 ⟨U₀.domRestrict v, hv.domRestrict⟩))
    {V : Set M} (hV : IsOpen V) {g : M → Y} (hg : ContinuousOn g V)
    {C' : Set X} (hC' : IsCompact C') (hC'U₀ : C' ⊆ U₀) (hvV : Set.MapsTo v C' V) :
    TendstoUniformlyOn (fun i ↦ g ∘ u i) (g ∘ v) l C' := by
  have hK : IsCompact (((↑) : U₀ → X) ⁻¹' C') :=
    IsInducing.subtypeVal.isCompact_preimage' hC' (by simpa [Subtype.range_coe_subtype] using hC'U₀)
  have hcoe := tendstoUniformlyOn_comp_of_tendsto hlim hV hg hK (fun x hx ↦ hvV hx)
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe] at hcoe ⊢
  intro s hs
  filter_upwards [hcoe s hs] with i hi x
  exact hi ⟨⟨x.val, hC'U₀ x.property⟩, x.property⟩

end Postcomp

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
