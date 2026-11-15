/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Order.Basic

/-!
# Continuity through a strictly monotone function

If `g` is strictly increasing on a neighbourhood `S` of `f x`, `f` maps a neighbourhood of `x`
into `S` and `g ∘ f` is continuous at `x`, then `f` is continuous at `x`
(`TauCeti.continuousAt_of_strictMonoOn_comp`). This recovers the continuity of a function `f`
defined implicitly by an equation `g (f y) = h y` with `h` continuous, without assuming that
the image of `f` is a neighbourhood of `f x`.

## Main results

* `TauCeti.eventually_gt_of_strictMonoOn_comp`: under these hypotheses, `f` stays above every
  `b < f x` near `x`.
* `TauCeti.continuousAt_of_strictMonoOn_comp`: under these hypotheses, `f` is continuous at `x`.
-/

public section

open Filter
open scoped Topology

namespace TauCeti

variable {X α β : Type*} [TopologicalSpace X]
  [LinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]
  [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
  {f : X → α} {g : α → β} {S : Set α} {x : X}

/-- If `g` is strictly increasing on a neighbourhood `S` of `f x`, `f` maps a neighbourhood of `x`
into `S` and `g ∘ f` is continuous at `x`, then `f` stays above every `b < f x` near `x`. -/
theorem eventually_gt_of_strictMonoOn_comp (hg : StrictMonoOn g S) (hS : S ∈ 𝓝 (f x))
    (hf : ∀ᶠ y in 𝓝 x, f y ∈ S) (hgf : ContinuousAt (g ∘ f) x) {b : α} (hb : b < f x) :
    ∀ᶠ y in 𝓝 x, b < f y := by
  obtain ⟨l, hl, hlS⟩ := exists_Ioc_subset_of_mem_nhds hS ⟨b, hb⟩
  obtain ⟨τ, hτ₁, hτ₂⟩ := exists_between (max_lt hl hb)
  have hτS : τ ∈ S := hlS ⟨(le_max_left _ _).trans_lt hτ₁, hτ₂.le⟩
  filter_upwards [hf, hgf.eventually (eventually_gt_nhds (hg hτS (mem_of_mem_nhds hS) hτ₂))]
    with y hy hgy
  exact ((le_max_right _ _).trans_lt hτ₁).trans ((hg.lt_iff_lt hτS hy).1 hgy)

/-- If `g` is strictly increasing on a neighbourhood `S` of `f x`, `f` maps a neighbourhood of `x`
into `S` and `g ∘ f` is continuous at `x`, then `f` is continuous at `x`. -/
theorem continuousAt_of_strictMonoOn_comp (hg : StrictMonoOn g S) (hS : S ∈ 𝓝 (f x))
    (hf : ∀ᶠ y in 𝓝 x, f y ∈ S) (hgf : ContinuousAt (g ∘ f) x) : ContinuousAt f x :=
  tendsto_order.2 ⟨fun _ hb ↦ eventually_gt_of_strictMonoOn_comp hg hS hf hgf hb,
    fun _ hb ↦ eventually_gt_of_strictMonoOn_comp (α := αᵒᵈ) (β := βᵒᵈ) hg.dual hS hf hgf hb⟩

end TauCeti
