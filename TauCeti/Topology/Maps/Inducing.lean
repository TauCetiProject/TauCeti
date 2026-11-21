/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Maps.Basic

/-!
# Convergence along inducing maps on subsets

If `g : X → Y` restricts to an inducing map on a subset `K ⊆ X` and a family `f : ι → X` eventually
takes values in `K`, then convergence of `g ∘ f` to `g p₀` for `p₀ ∈ K` implies convergence of `f`
to `p₀` (`Topology.IsInducing.tendsto_of_tendsto_comp_of_eventually_mem`).
-/

public section

open Filter Set Topology

namespace Topology.IsInducing

/-- If `g` restricts to an inducing map on `K` and `f` eventually takes values in `K`, convergence
of `g ∘ f` to `g p₀` for `p₀ ∈ K` gives convergence of `f` to `p₀`. -/
theorem tendsto_of_tendsto_comp_of_eventually_mem {ι X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {l : Filter ι} {g : X → Y} {K : Set X} (hg : IsInducing fun p : K ↦ g p)
    {f : ι → X} {p₀ : X} (hp₀ : p₀ ∈ K) (hfK : ∀ᶠ i in l, f i ∈ K)
    (hfg : Tendsto (fun i ↦ g (f i)) l (𝓝 (g p₀))) :
    Tendsto f l (𝓝 p₀) := by
  classical
  let f' : ι → K := fun i ↦ if h : f i ∈ K then ⟨f i, h⟩ else ⟨p₀, hp₀⟩
  have hf' : Tendsto f' l (𝓝 ⟨p₀, hp₀⟩) := hg.tendsto_nhds_iff.2 <|
    hfg.congr' (hfK.mono fun i hi ↦ by simp only [Function.comp_apply, f', hi, ↓reduceDIte])
  exact (((⟨rfl⟩ : IsInducing ((↑) : K → X)).tendsto_nhds_iff).1 hf').congr'
    (hfK.mono fun i hi ↦ by simp only [Function.comp_apply, f', hi, ↓reduceDIte])

end Topology.IsInducing
