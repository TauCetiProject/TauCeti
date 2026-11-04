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
continuous limit, composed with a continuous integrand.
-/

public section

open Set

variable {α β γ ι : Type*} [UniformSpace β] [UniformSpace γ]
  {F : ι → α → β} {f : α → β} {s : Set α} {g : β → γ} {p : Filter ι}

/-- Composing a family converging uniformly on `s` with a map continuous at every value of the
limit on `s` preserves uniform convergence on `s`, provided the values of the limit on `s` form a
compact set. -/
theorem ContinuousAt.comp_tendstoUniformlyOn_of_isCompact (hg : ∀ y ∈ f '' s, ContinuousAt g y)
    (hf : IsCompact (f '' s)) (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i x ↦ g (F i x)) (fun x ↦ g (f x)) p s := fun _ hu ↦ by
  filter_upwards [h _ (hf.uniformContinuousAt_of_continuousAt g hg hu)] with i hi x hx
  exact hi x hx (mem_image_of_mem f hx)
