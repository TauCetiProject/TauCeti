/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Approach
public import TauCeti.Analysis.Complex.Conformal.UpperHalfPlane
import TauCeti.Analysis.Complex.Conformal.Caratheodory
import Mathlib.Topology.Separation.Connected

/-!
# The Riemann map of a Jordan domain on the closed upper half-plane

Carathéodory's theorem extends the Riemann map of a Jordan domain to a homeomorphism from the
closed unit disc onto the closure of the domain. This file applies the generic closed-disc to
upper-half-plane transport to that map.

## Main statement

* TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier: the Riemann map
  of a Jordan domain, normalized to send infinity to a prescribed boundary point, as a continuous
  injection of the closed upper half-plane.
* `TauCeti.exists_injective_forall_eq_of_surjOn_im_eq_zero`: distinct real prevertices of distinct
  points of the image of the real line.
* `TauCeti.exists_prevertices_of_isJordanCurve_frontier`: a Carathéodory map of a bounded Jordan
  domain with real prevertices mapping to prescribed frontier points.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, Boundary Behaviour of Conformal Maps, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- Carathéodory's theorem on the closed upper half-plane. Let Ω be a bounded, connected
open subset of ℂ whose frontier is a Jordan curve, and let p be a point of that frontier. Then
there is a map which is continuous on the closed upper half-plane, holomorphic on the open upper
half-plane, a bijection from the open upper half-plane onto Ω, from the closed upper half-plane
onto closure Ω with p removed and from the real line onto frontier Ω with p removed, and which
tends to p at infinity within the closed half-plane. -/
theorem exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier {Ω : Set ℂ}
    (hΩo : IsOpen Ω) (hΩc : IsConnected Ω) (hΩb : IsBounded Ω)
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

/-- Real prevertices: if `f` maps the real line surjectively onto a set `T`, then distinct points
`v i` of `T` are the images `f (a i)` of distinct real numbers `a i`. -/
theorem exists_injective_forall_eq_of_surjOn_im_eq_zero {ι : Type*} {f : ℂ → ℂ} {T : Set ℂ}
    (hf : SurjOn f {z : ℂ | z.im = 0} T) {v : ι → ℂ} (hv : Injective v) (hvT : ∀ i, v i ∈ T) :
    ∃ a : ι → ℝ, Injective a ∧ ∀ i, f (a i) = v i := by
  choose x hx hfx using fun i => hf (hvT i)
  have hfa (i : ι) : f ((x i).re : ℂ) = v i := by
    rw [← hfx i]
    congr 1
    exact Complex.ext (by simp) (by simpa using (hx i).symm)
  exact ⟨fun i => (x i).re, fun i j (h : (x i).re = (x j).re) => hv (by rw [← hfa i, ← hfa j, h]),
    hfa⟩

/-- A Carathéodory map of the upper half-plane onto a bounded Jordan domain, sending infinity
to a frontier point `p` distinct from the specified points `v i`, together with real prevertices
`a i` mapping to those frontier points. -/
theorem exists_prevertices_of_isJordanCurve_frontier
    {ι : Type*} [Finite ι]
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsConnected U) (hUb : IsBounded U)
    (hUJ : IsJordanCurve (frontier U)) {v : ι → ℂ} (hv : Injective v)
    (hvU : ∀ i, v i ∈ frontier U) :
    ∃ f : ℂ → ℂ, ∃ a : ι → ℝ, ∃ p : ℂ, Injective a ∧
      DifferentiableOn ℂ f upperHalfPlaneSet ∧ ContinuousOn f {z : ℂ | 0 ≤ z.im} ∧
      InjOn f {z : ℂ | 0 ≤ z.im} ∧ BijOn f upperHalfPlaneSet U ∧ (∀ i, f (a i) = v i) ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 p) ∧
      p ∉ f '' {z : ℂ | 0 ≤ z.im} := by
  -- a boundary point `p` which is not a vertex: the frontier is infinite, the vertices finite
  obtain ⟨p, hpU, hpv⟩ : (frontier U \ range v).Nonempty :=
    ((hUJ.isConnected.isPreconnected.infinite_of_nontrivial
      (not_subsingleton_iff.mp hUJ.not_subsingleton)).sdiff (finite_range v)).nonempty
  obtain ⟨f, hfc, hfd, hfH, hfcl, hfR, hfp⟩ :=
    exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier hUo hUc hUb hUJ hpU
  obtain ⟨a, ha, hfa⟩ := exists_injective_forall_eq_of_surjOn_im_eq_zero hfR.surjOn hv
    fun i => ⟨hvU i, fun h => hpv ⟨i, h⟩⟩
  exact ⟨f, a, p, ha, hfd, hfc, hfcl.injOn, hfH, hfa, hfp,
    fun ⟨z, hz, hzp⟩ => (hfcl.mapsTo hz).2 hzp⟩

end TauCeti
