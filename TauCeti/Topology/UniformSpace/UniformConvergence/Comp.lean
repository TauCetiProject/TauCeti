/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Composing uniformly convergent families with continuous maps

Mathlib composes a uniformly convergent family with a uniformly continuous map
(`UniformContinuous.comp_tendstoUniformlyOn`). A map that is only continuous at the points of the
set of values of the limit suffices, provided that set is compact: by the Heine–Cantor argument
(`IsCompact.uniformContinuousAt_of_continuousAt`) the map is uniformly continuous at that compact
set, so it sends points close to it close to their images.

This applies, for instance, to families of paths converging uniformly on a compact interval to a
continuous limit, composed with a continuous integrand. To compose with a map that also depends on
the point `a` itself, as a time-dependent integrand does, first pass to the graphs
`a ↦ (a, F i a)`, which converge uniformly to the graph of the limit
(`TendstoUniformlyOn.graph`).

The file also records that a constant family converges uniformly
(`TauCeti.tendstoUniformlyOn_const`), and that two families converging uniformly along the same
filter converge jointly (`TendstoUniformlyOn.prodMk_same`), which is the form needed to compose
with maps of several variables.
-/

public section

open Filter Set

variable {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
  {F : ι → α → β} {f : α → β} {s : Set α} {g : β → γ} {p : Filter ι}

/-- Composing a family converging uniformly on `s` with a map continuous at every value of the
limit on `s` preserves uniform convergence on `s`, provided the values of the limit on `s` form a
compact set. -/
theorem IsCompact.comp_tendstoUniformlyOn (hf : IsCompact (f '' s))
    (hg : ∀ y ∈ f '' s, ContinuousAt g y) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i x ↦ g (F i x)) (fun x ↦ g (f x)) p s := fun _ hu ↦ by
  filter_upwards [h _ (hf.uniformContinuousAt_of_continuousAt g hg hu)] with i hi x hx
  exact hi x hx (mem_image_of_mem f hx)

namespace TauCeti

/-- A constant family converges uniformly to its value. -/
theorem tendstoUniformlyOn_const (f : α → β) (p : Filter ι) (s : Set α) :
    TendstoUniformlyOn (fun _ ↦ f) f p s :=
  fun _ hu ↦ .of_forall fun _ _ _ ↦ refl_mem_uniformity hu

end TauCeti

/-- Two families converging uniformly on `s` along the same filter converge jointly. Mathlib's
`TendstoUniformlyOn.prodMk` gives the joint convergence along the product filter `p ×ˢ p`. -/
theorem TendstoUniformlyOn.prodMk_same {F' : ι → α → γ} {f' : α → γ}
    (h : TendstoUniformlyOn F f p s) (h' : TendstoUniformlyOn F' f' p s) :
    TendstoUniformlyOn (fun i x ↦ (F i x, F' i x)) (fun x ↦ (f x, f' x)) p s :=
  fun _ hu ↦ Filter.tendsto_diag.eventually (h.prodMk h' _ hu)

/-- The graphs `a ↦ (a, F i a)` of a family converging uniformly on `s` converge uniformly on `s`
to the graph of the limit. -/
theorem TendstoUniformlyOn.graph [UniformSpace α] (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i a ↦ (a, F i a)) (fun a ↦ (a, f a)) p s := by
  rw [tendstoUniformlyOn_iff_tendsto] at h ⊢
  rw [uniformity_prod, tendsto_inf, tendsto_comap_iff, tendsto_comap_iff]
  refine ⟨?_, h⟩
  exact (tendsto_principal.2 (.of_forall fun _ ↦ SetRel.mem_id.2 rfl)).mono_right
    refl_le_uniformity
