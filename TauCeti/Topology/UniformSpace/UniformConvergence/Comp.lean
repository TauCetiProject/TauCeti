/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Composing uniformly convergent families with continuous maps

Mathlib composes a uniformly convergent family with a uniformly continuous map
(`UniformContinuous.comp_tendstoUniformlyOn`). A map that is only continuous at the points of the
set of values of the limit suffices, provided that set is compact: by the Heine–Cantor argument
(`IsCompact.uniformContinuousAt_of_continuousAt`) the map is uniformly continuous at that compact
set, so it sends points close to it close to their images.

This applies, for instance, to families of paths converging uniformly on a compact interval to a
continuous limit, composed with a continuous integrand.

For coefficients `P (x, y)` that depend on both the point `x` and the value `y`, continuity on a
compact product `s ×ˢ t` suffices when all the values lie in `t`
(`IsCompact.tendstoUniformlyOn_comp_prodMk`): `P` is then uniformly continuous there. This is the
form in which the coefficients `J(z, u(z))` of a nonlinear equation converge along a sequence of
maps `u` converging uniformly on a compact set.
-/

public section

open Set

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

/-- Let `Fᵢ → f` uniformly on a compact set `s`, with all values on `s` in a compact set `t`. Then
`P (x, Fᵢ x) → P (x, f x)` uniformly on `s`, for every `P` continuous on `s ×ˢ t`. -/
theorem IsCompact.tendstoUniformlyOn_comp_prodMk {α β γ : Type*} [PseudoMetricSpace α]
    [PseudoMetricSpace β] [PseudoMetricSpace γ] {s : Set α} {t : Set β} {F : ι → α → β}
    {f : α → β} {P : α × β → γ} (hs : IsCompact s) (ht : IsCompact t)
    (hP : ContinuousOn P (s ×ˢ t)) (hF : ∀ᶠ i in p, MapsTo (F i) s t) (hf : MapsTo f s t)
    (h : TendstoUniformlyOn F f p s) :
    TendstoUniformlyOn (fun i x ↦ P (x, F i x)) (fun x ↦ P (x, f x)) p s := by
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
  obtain ⟨δ, hδ, hPδ⟩ :=
    Metric.uniformContinuousOn_iff.1 ((hs.prod ht).uniformContinuousOn_of_continuous hP) ε hε
  filter_upwards [hF, Metric.tendstoUniformlyOn_iff.1 h δ hδ] with i hFi hi x hx
  exact hPδ _ ⟨hx, hf hx⟩ _ ⟨hx, hFi hx⟩ (by simpa [Prod.dist_eq] using hi x hx)
