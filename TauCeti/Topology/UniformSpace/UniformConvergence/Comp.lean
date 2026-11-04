/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Topology.UniformSpace.UniformConvergenceTopology

/-!
# Composing uniformly convergent families with continuous maps

Mathlib composes a uniformly convergent family with a map that is uniformly continuous on a set
containing its values (`UniformContinuousOn.comp_tendstoUniformlyOn_eventually`). In a proper
metric space a continuous map suffices, provided the values of the limit on the set form a
compact set: the closed `1`-thickening of that compact set is compact, the map is uniformly
continuous on it by the Heine–Cantor theorem, and the family eventually takes its values there.

This applies, for instance, to families of paths converging uniformly on a compact interval to a
continuous limit, composed with a continuous integrand.
-/

public section

open Filter Metric Set

variable {α β γ ι : Type*} [PseudoMetricSpace β] [ProperSpace β] [UniformSpace γ]
  {F : ι → α → β} {f : α → β} {s : Set α} {g : β → γ} {p : Filter ι}

/-- In a proper metric space, composing a family converging uniformly on `s` with a continuous map
preserves uniform convergence on `s`, provided the values of the limit on `s` form a compact
set. -/
theorem TendstoUniformlyOn.comp_continuous_of_isCompact (h : TendstoUniformlyOn F f p s)
    (hg : Continuous g) (hf : IsCompact (f '' s)) :
    TendstoUniformlyOn (fun i x ↦ g (F i x)) (fun x ↦ g (f x)) p s := by
  -- The family eventually takes values in the compact `1`-thickening of `f '' s`.
  have hF : ∀ᶠ i in p, ∀ x ∈ s, F i x ∈ cthickening 1 (f '' s) := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp h 1 one_pos] with i hi x hx
    exact mem_cthickening_of_dist_le _ _ _ _ (mem_image_of_mem f hx)
      (by simpa only [dist_comm] using (hi x hx).le)
  exact UniformContinuousOn.comp_tendstoUniformlyOn_eventually hF
    (fun x hx ↦ self_subset_cthickening _ (mem_image_of_mem f hx))
    (hf.cthickening.uniformContinuousOn_of_continuous hg.continuousOn) h
