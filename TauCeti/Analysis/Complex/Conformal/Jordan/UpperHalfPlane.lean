/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Approach
public import TauCeti.Analysis.Complex.Conformal.UpperHalfPlane
import TauCeti.Analysis.Complex.Conformal.Caratheodory

/-!
# The Riemann map of a Jordan domain on the closed upper half-plane

Carathéodory's theorem extends the Riemann map of a Jordan domain to a homeomorphism from the
closed unit disc onto the closure of the domain. This file applies the generic closed-disc to
upper-half-plane transport to that map.

## Main statement

* TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier: the Riemann map
  of a Jordan domain, normalized to send infinity to a prescribed boundary point, as a continuous
  injection of the closed upper half-plane.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, Boundary Behaviour of Conformal Maps, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Metric Set Topology

namespace TauCeti

/-- Carathéodory's theorem on the closed upper half-plane. Let Ω be a bounded, simply connected
open subset of ℂ whose frontier is a Jordan curve, and let p be a point of that frontier. Then
there is a map which is continuous on the closed upper half-plane, holomorphic on the open upper
half-plane, a bijection from the open upper half-plane onto Ω, from the closed upper half-plane
onto closure Ω with p removed and from the real line onto frontier Ω with p removed, and which
tends to p at infinity within the closed half-plane. -/
theorem exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsSimplyConnected Ω) (hΩb : IsBounded Ω)
    (hΩJ : IsJordanCurve (frontier Ω)) {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ f : ℂ → ℂ, ContinuousOn f {z | 0 ≤ z.im} ∧
      DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet ∧
      BijOn f UpperHalfPlane.upperHalfPlaneSet Ω ∧ BijOn f {z | 0 ≤ z.im} (closure Ω \ {p}) ∧
      BijOn f {z | z.im = 0} (frontier Ω \ {p}) ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 p) := by
  obtain ⟨g, hgc, hgd, hgΩ⟩ :=
    exists_continuousOn_closedBall_bijOn_ball_of_isJordanCurve_frontier hΩo hΩc hΩb hΩJ
  have himg : g '' ball 0 1 = Ω := hgΩ.image_eq
  exact exists_continuousOn_bijOn_upperHalfPlaneSet_of_injOn_closedBall hgc hgd
    (injOn_closedBall_of_isJordanCurve_frontier one_pos hgd hgΩ.injOn (himg ▸ hΩb) (himg ▸ hΩJ)
      hgc fun _ _ => rfl) himg hp

end TauCeti
