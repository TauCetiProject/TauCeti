/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Approach
public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.Transport
public import TauCeti.Analysis.Complex.Conformal.PrimeEnd.UnitDisc

/-!
# The prime ends of a Jordan domain are the points of the circle

Let `Ω` be a bounded domain whose frontier is a Jordan curve. By Carathéodory's theorem a Riemann
map of the unit disc onto `Ω` extends to a homeomorphism `g` of the closed disc onto the closure
of `Ω`. Such a map transports prime ends (`TauCeti.PrimeEnd.map`), and the prime ends of the disc
are the points of the unit circle (`TauCeti.unitDiscPrimeEnd_bijective`). So `g` carries the
radial prime end of the disc at each point of the circle to a prime end of `Ω`, and every prime end
of `Ω` arises in this way from exactly one point of the circle. So the prime ends of `Ω` are in
bijection with the points of the unit circle, which Carathéodory's extension identifies with the
boundary points of `Ω`; this is the case that Carathéodory's theory of prime ends generalizes.

## Main declarations

* `TauCeti.exists_bijective_primeEnd_map_unitDiscPrimeEnd_of_isJordanCurve_frontier` -- the
  extension of a Riemann map to the closed disc induces a bijection from the unit circle onto the
  prime ends of a bounded Jordan domain.

## References

* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Sections 2.1 and 2.4.
* C. Carathéodory, *Über die Begrenzung einfach zusammenhängender Gebiete*, Math. Ann. 73
  (1913).
-/

public section

noncomputable section

open Bornology Function Metric Set

namespace TauCeti

/-- **The prime ends of a Jordan domain are the points of the circle.** Let `Ω` be a bounded
domain whose frontier is a Jordan curve. There is a holomorphic bijection `g` of the unit disc onto
`Ω` that is continuous and injective on the closed disc, and the map of prime ends it induces sends
the radial prime ends of the disc at the points of the unit circle bijectively onto the prime ends
of `Ω`. -/
theorem exists_bijective_primeEnd_map_unitDiscPrimeEnd_of_isJordanCurve_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) :
    ∃ (g : ℂ → ℂ) (hgc : ContinuousOn g (closure (ball 0 1)))
      (hgi : InjOn g (closure (ball 0 1))) (hg : g '' ball 0 1 = Ω),
      DifferentiableOn ℂ g (ball 0 1) ∧
        Bijective fun ζ : sphere (0 : ℂ) 1 =>
          PrimeEnd.map isBounded_ball isOpen_ball hgc hgi hg (unitDiscPrimeEnd ζ) := by
  obtain ⟨g, hgc, hgd, hgb, e, he⟩ :=
    exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier hΩo hΩc hΩb hΩJ
  rw [← closure_ball (0 : ℂ) one_ne_zero] at hgc
  -- `g` agrees with the homeomorphism `e` on the closed disc, so it is injective there.
  have hgi : InjOn g (closure (ball 0 1)) := by
    rw [closure_ball (0 : ℂ) one_ne_zero]
    intro z hz w hw hzw
    have h : e ⟨z, hz⟩ = e ⟨w, hw⟩ := Subtype.ext (by rw [he, he]; exact hzw)
    exact congrArg Subtype.val (e.injective h)
  exact ⟨g, hgc, hgi, hgb.image_eq, hgd,
    PrimeEnd.map_bijective.comp unitDiscPrimeEnd_bijective⟩

end TauCeti

end
