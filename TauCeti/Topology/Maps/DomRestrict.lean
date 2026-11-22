/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic

/-!
# Restrictions of maps

The restriction `s.domRestrict f` of a map `f : X → Y` to a subset `s ⊆ X` is an open map exactly
when, for each point `x ∈ s`, the image under `f` of every neighbourhood of `x` in `s` is a
neighbourhood of `f x` (`TauCeti.isOpenMap_domRestrict_iff`). The relatively open subsets of `s`
are the traces `t ∩ s` of open sets of `X`, so this is a pointwise test that does not mention the
subtype topology. When `f` is the projection of a cylinder to its base, it describes the sets whose
projection is open on every relatively open subset.

If `g : X → Y` restricts to an inducing map on a subset `K ⊆ X` and a family `f : ι → X` eventually
takes values in `K`, then convergence of `g ∘ f` to `g p₀` for `p₀ ∈ K` implies convergence of `f`
to `p₀` (`Topology.IsInducing.tendsto_of_tendsto_comp_of_eventually_mem`).
-/

public section

open Filter Set Topology

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The restriction of `f` to `s` is an open map if and only if, for every `x ∈ s` and every
neighbourhood `t` of `x`, the image `f '' (t ∩ s)` is a neighbourhood of `f x`. -/
theorem isOpenMap_domRestrict_iff {f : X → Y} {s : Set X} :
    IsOpenMap (s.domRestrict f) ↔ ∀ x ∈ s, ∀ t ∈ 𝓝 x, f '' (t ∩ s) ∈ 𝓝 (f x) := by
  refine ⟨fun h x hx t ht ↦ ?_, fun h V hV ↦ ?_⟩
  · rw [← image_domRestrict]
    exact h.image_mem_nhds (x := ⟨x, hx⟩) (continuous_subtypeVal.continuousAt.preimage_mem_nhds ht)
  · obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.1 hV
    rw [image_domRestrict, isOpen_iff_mem_nhds]
    rintro _ ⟨x, ⟨hxt, hxs⟩, rfl⟩
    exact h x hxs t (ht.mem_nhds hxt)

end TauCeti

namespace Topology.IsInducing

/-- If `g` restricts to an inducing map on `K` and `f` eventually takes values in `K`, convergence
of `g ∘ f` to `g p₀` for `p₀ ∈ K` gives convergence of `f` to `p₀`. -/
theorem tendsto_of_tendsto_comp_of_eventually_mem {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {l : Filter ι} {g : X → Y} {K : Set X} (hg : IsInducing (K.domRestrict g))
    {f : ι → X} {p₀ : X} (hp₀ : p₀ ∈ K) (hfK : ∀ᶠ i in l, f i ∈ K)
    (hfg : Tendsto (fun i ↦ g (f i)) l (𝓝 (g p₀))) :
    Tendsto f l (𝓝 p₀) := by
  classical
  let f' : ι → K := fun i ↦ if h : f i ∈ K then ⟨f i, h⟩ else ⟨p₀, hp₀⟩
  have hf' : Tendsto f' l (𝓝 ⟨p₀, hp₀⟩) := hg.tendsto_nhds_iff.2 <|
    hfg.congr' (hfK.mono fun i hi ↦ by simp only [Function.comp_apply, domRestrict_apply, f', hi,
      ↓reduceDIte])
  exact (((⟨rfl⟩ : IsInducing ((↑) : K → X)).tendsto_nhds_iff).1 hf').congr'
    (hfK.mono fun i hi ↦ by simp only [Function.comp_apply, f', hi, ↓reduceDIte])

end Topology.IsInducing
