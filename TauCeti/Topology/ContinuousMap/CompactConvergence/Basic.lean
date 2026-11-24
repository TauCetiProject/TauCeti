/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.CompactConvergence

/-!
# Compact convergence: boundedness and postcomposition

For a topological space `X` and a uniform space `E`, the continuous maps `C(X, E)` carry the
uniformity of compact convergence (`ContinuousMap.compactConvergenceUniformSpace`). This file
records two basic properties of compact convergence:

* **Boundedness of totally bounded families:** a totally bounded family of continuous maps takes
  totally bounded sets of values on each compact subset of `X`. For a seminormed group target this
  bounds the norms of the whole family on each compact set at once, which is how relatively compact
  families of continuous maps are shown to be locally bounded. The proof adapts the finite-cover
  argument behind Mathlib's `TotallyBounded.isBounded` to compact convergence: finitely many maps
  approximate the whole family uniformly on `K`, and each of them has a compact, hence totally
  bounded, image of `K`.
* **Postcomposition under compact-open convergence:** if continuous maps `u i → v` into a
  topological space `M` in the compact-open topology, and `g : M → Y` into a uniform space is
  continuous on an open set `V` containing `v '' C'` for a compact `C'`, then `g ∘ u i → g ∘ v`
  uniformly on `C'`.

## Main results

* `TotallyBounded.biUnion_image`: if `A ⊆ C(X, E)` is totally bounded and `K ⊆ X` is compact, then
  the set `⋃ g ∈ A, g '' K` of all values on `K` is totally bounded.
* `ContinuousMap.tendstoUniformlyOn_comp_of_tendsto` and
  `ContinuousMap.tendstoUniformlyOn_comp_of_tendsto_domRestrict`: postcomposing compact-open
  convergent maps with a map continuous on an open neighbourhood of the limit image yields uniform
  convergence on compact subsets.
-/

public section

open Set Uniformity

namespace TotallyBounded

variable {X E : Type*} [TopologicalSpace X] [UniformSpace E]

/-- The values on a compact set `K` of a totally bounded family `A` of continuous maps, for the
uniformity of compact convergence, form a totally bounded set. -/
theorem biUnion_image {A : Set C(X, E)} (hA : TotallyBounded A) {K : Set X}
    (hK : IsCompact K) : TotallyBounded (⋃ g ∈ A, g '' K) := by
  intro V hV
  obtain ⟨W, hW, hWV⟩ := comp_mem_uniformity_sets hV
  -- Finitely many maps `g ∈ t` approximate every member of `A` within `W`, uniformly on `K`.
  obtain ⟨t, ht, hAt⟩ :=
    ContinuousMap.hasBasis_compactConvergenceUniformity.totallyBounded_iff.mp hA (K, W) ⟨hK, hW⟩
  -- Their values on `K` form a compact, hence totally bounded, set.
  obtain ⟨s, hs, hts⟩ :=
    (ht.isCompact_biUnion fun g _ => hK.image g.continuous).totallyBounded W hW
  refine ⟨s, hs, iUnion₂_subset fun f hf => ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨g, hg, hfg⟩ := mem_iUnion₂.mp (hAt hf)
  obtain ⟨y, hy, hgy⟩ := mem_iUnion₂.mp (hts (mem_biUnion hg (mem_image_of_mem g hx)))
  exact mem_biUnion hy (hWV (SetRel.prodMk_mem_comp (hfg x hx) hgy))

end TotallyBounded

namespace ContinuousMap

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
