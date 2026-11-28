/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformApproximation
import TauCeti.Topology.Compactness.Compact

/-!
# Locally uniform limits read back in a compact space

Compactness theorems for maps `uᵢ` into a compact space `X`, such as a closed manifold, are often
proved for the maps `f ∘ uᵢ` read through a continuous injection `f : X → Y` into a uniform
space, such as a Whitney embedding. If the maps `f ∘ uᵢ` are continuous and converge locally
uniformly on a set `s` to `g`, then `g` is continuous on `s` and takes values in the closed set
`f(X)`, so it is read back in `X`: `g = f ∘ y` on `s` for a map `y` continuous on `s`, to which
the `uᵢ` converge pointwise on `s` (`TendstoLocallyUniformlyOn.exists_tendsto_of_comp`). This is
the pointwise read-back `IsCompact.exists_tendsto_of_tendsto_comp` for locally uniform limits.
-/

public section

open Filter Set Topology

/-- **Locally uniform limits read back in a compact space.** Let `f : X → Y` be a continuous
injection from a compact space into a Hausdorff uniform space, and let the maps `f ∘ xᵢ`,
frequently continuous on `s`, converge locally uniformly on `s` to `g` along `l`. Then there is a
map `y` continuous on `s` such that the `f ∘ xᵢ` converge locally uniformly on `s` to `f ∘ y` and
the `xᵢ` converge pointwise on `s` to `y`. -/
theorem TendstoLocallyUniformlyOn.exists_tendsto_of_comp {α X Y ι : Type*} [TopologicalSpace α]
    [TopologicalSpace X] [CompactSpace X] [UniformSpace Y] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) {l : Filter ι} [l.NeBot] {s : Set α}
    {x : ι → α → X} {g : α → Y} (h : TendstoLocallyUniformlyOn (fun i ↦ f ∘ x i) g l s)
    (hc : ∃ᶠ i in l, ContinuousOn (f ∘ x i) s) :
    ∃ y : α → X, ContinuousOn y s ∧ TendstoLocallyUniformlyOn (fun i ↦ f ∘ x i) (f ∘ y) l s ∧
      ∀ a ∈ s, Tendsto (fun i ↦ x i a) l (𝓝 (y a)) := by
  obtain ⟨y, hy, -, hfy, hpt⟩ := isCompact_univ.exists_tendsto_of_tendsto_comp hf.continuousOn
    hinj.injOn (fun _ _ ↦ .of_forall fun _ ↦ mem_univ _) (h.continuousOn hc)
    fun a ha ↦ h.tendsto_at ha
  exact ⟨y, hy, h.congr_right hfy.symm, hpt⟩
