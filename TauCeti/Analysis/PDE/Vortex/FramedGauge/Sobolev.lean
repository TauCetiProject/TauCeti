/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.FramedGauge.Basic
public import TauCeti.Analysis.Sobolev.BesselPotential.CircleGroup

/-!
# The Banach framed gauge group and the smooth framed gauge group

For `s > 1` the Banach gauge group of framed plane vortices is
`TauCeti.sobolevCircleGroup ℂ s hs`: continuous maps `u : ℂ → Circle` with `u - 1 ∈ H^s(ℂ; ℂ)`.
Its elements tend to one at infinity, so a smooth element is a smooth framed gauge
(`TauCeti.Vortex.mem_framedGaugeGroup_of_mem_sobolevCircleGroup`). Smooth gauges with `u - 1`
compactly supported lie in both groups (`TauCeti.mem_sobolevCircleGroup_of_hasCompactSupport`).
The smooth framed gauge group `TauCeti.Vortex.framedGaugeGroup` imposes no decay rate on `u - 1`,
so it is a separate group rather than a subgroup of the Banach completion; a smooth phase with a
`1 / |z|` tail, for instance, is not square integrable on the plane.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Birkhäuser, 1980, Chapter III.
-/

public section

open Module
open scoped ContDiff

namespace TauCeti.Vortex

/-- **Smooth elements of the Banach gauge group are smooth framed gauges.** For `s > 1`, a smooth
map `u : ℂ → Circle` in `sobolevCircleGroup ℂ s hs` lies in `framedGaugeGroup`, since elements of
the Banach gauge group tend to one at infinity. -/
theorem mem_framedGaugeGroup_of_mem_sobolevCircleGroup {s : ℝ}
    {hs : finrank ℝ ℂ < 2 * s} {u : ℂ → Circle} (hu : u ∈ sobolevCircleGroup ℂ s hs)
    (hsmooth : ContDiff ℝ ∞ fun z ↦ (u z : ℂ)) : u ∈ framedGaugeGroup :=
  (mem_framedGaugeGroup u).2 ⟨hsmooth, tendsto_cocompact_of_mem_sobolevCircleGroup hu⟩

end TauCeti.Vortex
