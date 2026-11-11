/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# Images of open simply connected sets under injective holomorphic maps

A holomorphic map that is injective on an open set `Ω ⊆ ℂ` carries `Ω` to an open set, and carries
a simply connected `Ω` to a simply connected set. Openness is used by the Riemann mapping theorem
(in the Koebe square-root step); the transport of simple connectivity is a standalone topological
fact, which that proof does not need, since it carries holomorphic square roots across such a map
instead (`TauCeti.HasHolomorphicSquareRoots.image`).

## The argument

Openness is the local open mapping theorem
(`AnalyticAt.eventually_constant_or_nhds_le_map_nhds`), so it needs no connectivity hypothesis on
`Ω`: at each point of `Ω` the map `g` is analytic, and it is not locally constant there because it
is injective and `ℂ` has no isolated points.

Simple connectivity is then purely topological, and Mathlib supplies it: injectivity, continuity
and openness make `Ω.domRestrict g` an open embedding, hence a homeomorphism onto its range
`g '' Ω`, and simple connectivity is invariant under homotopy equivalence. Holomorphy enters *only*
through the open mapping theorem; there is no separate homotopy argument here.

## Main statements

* `TauCeti.isOpen_image_of_differentiableOn_of_injOn` — the image of an open set is open.
* `TauCeti.isOpenEmbedding_domRestrict_of_differentiableOn_of_injOn` — restricted to its open
  domain, the map is an open embedding into `ℂ`.
* `TauCeti.isSimplyConnected_image_of_differentiableOn_of_injOn` — the image of an open simply
  connected set is simply connected.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 4 §3.4 (the open mapping theorem).
-/

public section

namespace TauCeti

open Complex Set Filter Topology

variable {Ω : Set ℂ} {g : ℂ → ℂ}

/-- **The image of an open set under an injective holomorphic map is open.** No connectivity
hypothesis on `Ω` is needed. -/
theorem isOpen_image_of_differentiableOn_of_injOn (hΩo : IsOpen Ω)
    (hgd : DifferentiableOn ℂ g Ω) (hgi : InjOn g Ω) : IsOpen (g '' Ω) := by
  refine isOpen_iff_mem_nhds.mpr ?_
  rintro _ ⟨z, hz, rfl⟩
  have hΩz : Ω ∈ 𝓝 z := hΩo.mem_nhds hz
  rcases (hgd.analyticAt hΩz).eventually_constant_or_nhds_le_map_nhds with hconst | hle
  · -- `g` cannot be constant near `z`: injectivity would make `z` an isolated point of `ℂ`.
    obtain ⟨w, ⟨hgw, hw⟩, hwz⟩ := ((hconst.and hΩz).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin (s := {z}ᶜ)) |>.exists
    exact absurd (hgi hw hz hgw) hwz
  · exact hle (image_mem_map hΩz)

/-- Restricted to its open domain, an injective holomorphic map is an open embedding into `ℂ`. -/
theorem isOpenEmbedding_domRestrict_of_differentiableOn_of_injOn (hΩo : IsOpen Ω)
    (hgd : DifferentiableOn ℂ g Ω) (hgi : InjOn g Ω) : IsOpenEmbedding (Ω.domRestrict g) := by
  refine .of_continuous_injective_isOpenMap
    (continuousOn_iff_continuous_domRestrict.mp hgd.continuousOn) (injOn_iff_injective.mp hgi) ?_
  intro V hV
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.mp hV
  rw [image_domRestrict]
  exact isOpen_image_of_differentiableOn_of_injOn (hW.inter hΩo) (hgd.mono inter_subset_right)
    (hgi.mono inter_subset_right)

/-- **Injective holomorphic maps preserve simple connectivity.** The image of an open simply
connected set under a holomorphic map injective on it is again simply connected. -/
theorem isSimplyConnected_image_of_differentiableOn_of_injOn (hΩo : IsOpen Ω)
    (hΩc : IsSimplyConnected Ω) (hgd : DifferentiableOn ℂ g Ω) (hgi : InjOn g Ω) :
    IsSimplyConnected (g '' Ω) := by
  have := hΩc.simplyConnectedSpace
  rw [← range_domRestrict]
  -- `IsSimplyConnected s` is by definition `SimplyConnectedSpace ↥s`.
  exact (isOpenEmbedding_domRestrict_of_differentiableOn_of_injOn hΩo hgd hgi).isEmbedding
    |>.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace

end TauCeti
