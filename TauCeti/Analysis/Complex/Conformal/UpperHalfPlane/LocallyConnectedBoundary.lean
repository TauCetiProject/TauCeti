/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.UpperHalfPlane
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.Topology.ClusterSet

import TauCeti.Analysis.Complex.Conformal.Caratheodory
import TauCeti.Analysis.Complex.Conformal.Inverse.BoundaryCluster
import TauCeti.Data.Set.Image

/-!
# Upper-half-plane maps with locally connected boundary

Carathéodory's continuity theorem extends a Riemann map to the closed disc when the target has
locally connected boundary, but the extension need not be injective there.  This file transports
that extension to the closed upper half-plane while retaining the exact interior bijection and the
boundary correspondence.

The boundary point omitted by the Cayley transform is the limit at infinity.  Other points of the
source circle can have the same boundary value, so the finite real boundary values cover the target
frontier up to that distinguished point rather than necessarily omitting it.  Such a repeated value
is excluded at every boundary point where the target has preconnected approach regions: there the
real fibre of the extension has at most one point.

## Main statement

* `TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_continuousOn_closedBall` -- transport
  of a continuous closed-disc extension without a boundary-injectivity hypothesis.
* `TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier` -- a
  Riemann map of a bounded simply connected domain with locally connected boundary, transported to
  the upper half-plane with a prescribed boundary limit at infinity.
* `TauCeti.subsingleton_real_fiber_of_isPreconnectedApproachAt` -- the boundary extension is
  injective over every boundary point at which the image has preconnected approach regions.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

/-- **Transport of a continuous closed-disc extension to the upper half-plane.** Suppose `g` is
continuous on the closed unit disc and conformally maps its interior onto `Ω`. Given a point `p` of
the frontier of `Ω`, precomposition with a rotated Cayley transform gives a conformal map from the
upper half-plane onto `Ω` which extends continuously to the real axis and tends to `p` at infinity.

The finite real boundary values lie in `frontier Ω` and, together with `p`, cover that frontier.
No injectivity is asserted on the real axis. -/
theorem exists_continuousOn_bijOn_upperHalfPlaneSet_of_continuousOn_closedBall
    {g : ℂ → ℂ} {Ω : Set ℂ} (hgc : ContinuousOn g (closedBall 0 1))
    (hgd : DifferentiableOn ℂ g (ball 0 1)) (hgΩ : BijOn g (ball 0 1) Ω)
    {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ f : ℂ → ℂ, ContinuousOn f {z | 0 ≤ z.im} ∧
      DifferentiableOn ℂ f upperHalfPlaneSet ∧ BijOn f upperHalfPlaneSet Ω ∧
      insert p (f '' {z | 0 ≤ z.im}) = closure Ω ∧
      insert p (f '' {z | z.im = 0}) = frontier Ω ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 p) := by
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hgcl : g '' closedBall 0 1 = closure Ω := by
    rw [← hcl, image_closure_eq_closure_image isBounded_ball (hcl ▸ hgc)
      (fun _ _ => rfl), hgΩ.image_eq]
  have hgfr : g '' sphere 0 1 = frontier Ω := by
    rw [← frontier_ball 0 one_ne_zero]
    exact (image_frontier_eq_frontier_image isOpen_ball isBounded_ball hgd hgΩ.injOn
      (hcl ▸ hgc) fun _ _ => rfl).trans (congrArg frontier hgΩ.image_eq)
  obtain ⟨ζ, hζ, hζp⟩ : ∃ ζ ∈ sphere (0 : ℂ) 1, g ζ = p := by
    have hp' := hp
    rw [← hgfr] at hp'
    exact hp'
  have hζnorm : ‖ζ‖ = 1 := mem_sphere_zero_iff_norm.mp hζ
  obtain ⟨hrotK, hrotH⟩ := bijOn_mul_left_of_norm_eq_one hζnorm
  set c : ℂ → ℂ := fun z => ζ * ((z - Complex.I) / (z + Complex.I))
  have hcH : BijOn c upperHalfPlaneSet (ball 0 1) :=
    hrotH.comp bijOn_sub_I_div_add_I_upperHalfPlaneSet
  have hcK : BijOn c {z | 0 ≤ z.im} (closedBall 0 1 \ {ζ}) :=
    hrotK.comp bijOn_sub_I_div_add_I_im_nonneg
  have hcd : DifferentiableOn ℂ c {z | 0 ≤ z.im} :=
    (differentiableOn_const ζ).mul differentiableOn_sub_I_div_add_I_im_nonneg
  have hct : Tendsto c (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝[closedBall 0 1] ζ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_inf_principal.mpr
      (Eventually.of_forall fun z hz => (hcK.mapsTo hz).1)⟩
    simpa [c] using (tendsto_sub_I_div_add_I_cobounded.const_mul ζ).mono_left inf_le_left
  have hreal : {z : ℂ | z.im = 0} = {z | 0 ≤ z.im} \ upperHalfPlaneSet := by
    ext z
    simp only [Set.mem_sdiff, upperHalfPlaneSet, mem_ofPred_eq]
    exact ⟨fun h => ⟨h.ge, not_lt.mpr h.le⟩,
      fun h => le_antisymm (not_lt.mp h.2) h.1⟩
  have hcR : BijOn c {z : ℂ | z.im = 0} (sphere 0 1 \ {ζ}) := by
    have h := (hcK.injOn.mono (sdiff_subset (t := upperHalfPlaneSet))).bijOn_image
    rw [hcK.injOn.image_sdiff_subset (ofPred_subset_ofPred.mpr fun _ => le_of_lt), hcK.image_eq,
      hcH.image_eq, sdiff_right_comm, closedBall_sdiff_ball, ← hreal] at h
    exact h
  have hH : BijOn (g ∘ c) upperHalfPlaneSet Ω := (hgΩ).comp hcH
  have hK : insert p ((g ∘ c) '' {z : ℂ | 0 ≤ z.im}) = closure Ω := by
    rw [← hζp, insert_image_comp_of_image_eq_sdiff_singleton hcK.image_eq
      (sphere_subset_closedBall hζ), hgcl]
  have hR : insert p ((g ∘ c) '' {z : ℂ | z.im = 0}) = frontier Ω := by
    rw [← hζp, insert_image_comp_of_image_eq_sdiff_singleton hcR.image_eq hζ, hgfr]
  refine ⟨g ∘ c, hgc.comp hcd.continuousOn fun z hz => (hcK.mapsTo hz).1,
    hgd.comp (hcd.mono (ofPred_subset_ofPred.mpr fun _ => le_of_lt)) hcH.mapsTo, hH, hK, hR,
    by simpa [hζp] using (hgc ζ (mem_closedBall.mpr hζ.le)).tendsto.comp hct⟩

/-- **Carathéodory's continuity theorem on the upper half-plane.** Let `Ω` be a bounded simply
connected open subset of `ℂ` with locally connected frontier, and let `p ∈ frontier Ω`. Then a
Riemann map from the upper half-plane onto `Ω` extends continuously to the real axis and tends to
`p` at infinity.

The finite real boundary values lie in `frontier Ω` and, together with `p`, cover that frontier.
No injectivity is asserted on the real axis: distinct boundary parameters can have the same value
when the frontier is locally connected but is not a Jordan curve. -/
theorem exists_continuousOn_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩs : IsSimplyConnected Ω) (hΩb : IsBounded Ω)
    [LocallyConnectedSpace (frontier Ω)] {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ f : ℂ → ℂ, ContinuousOn f {z | 0 ≤ z.im} ∧
      DifferentiableOn ℂ f upperHalfPlaneSet ∧ BijOn f upperHalfPlaneSet Ω ∧
      insert p (f '' {z | 0 ≤ z.im}) = closure Ω ∧
      insert p (f '' {z | z.im = 0}) = frontier Ω ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 p) := by
  obtain ⟨g, hgc, hgd, hgΩ⟩ :=
    exists_continuousOn_closedBall_bijOn_ball_of_locallyConnectedSpace_frontier hΩo hΩs hΩb
  exact exists_continuousOn_bijOn_upperHalfPlaneSet_of_continuousOn_closedBall hgc hgd hgΩ hp

/-- **A boundary point with preconnected approach regions has at most one real prevertex.** Let
`F` be continuous on the closed upper half-plane, holomorphic and injective on the open
half-plane, and have a limit at infinity. If the image `F '' upperHalfPlaneSet` has preconnected
approach regions at a point `a`, then at most one real parameter is sent to `a`.

No condition is placed at the other boundary points, so distinct real parameters can still share a
boundary value where the image does not have preconnected approach regions. -/
theorem subsingleton_real_fiber_of_isPreconnectedApproachAt {F : ℂ → ℂ} {p a : ℂ}
    (hFc : ContinuousOn F {z | 0 ≤ z.im}) (hFd : DifferentiableOn ℂ F upperHalfPlaneSet)
    (hFi : InjOn F upperHalfPlaneSet)
    (hp : Tendsto F (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 p))
    (hloc : IsPreconnectedApproachAt (F '' upperHalfPlaneSet) a) :
    {x : ℝ | F x = a}.Subsingleton := by
  -- Pull `F` back to the closed disc by the inverse Cayley transform `κ`, filling in `p` at the
  -- omitted boundary point `1`, and apply the disc form of the statement.
  set κ : ℂ → ℂ := fun w => Complex.I * (1 + w) / (1 - w)
  have hκK : BijOn κ (closedBall 0 1 \ {1}) {z | 0 ≤ z.im} :=
    bijOn_I_mul_one_add_div_one_sub_closedBall_sdiff
  have hκH : BijOn κ (ball 0 1) upperHalfPlaneSet := bijOn_I_mul_one_add_div_one_sub_ball
  have hκc {w : ℂ} (hw : w ≠ 1) : ContinuousAt κ w :=
    (hasDerivAt_I_mul_one_add_div_one_sub hw).continuousAt
  have hball1 {w : ℂ} (hw : w ∈ ball (0 : ℂ) 1) : w ≠ 1 :=
    ne_of_mem_ball_of_norm_eq_one hw norm_one
  have hGc : ContinuousOn (update (F ∘ κ) 1 p) (closedBall 0 1) := by
    refine continuousOn_update_iff.mpr ⟨fun w hw => ?_, fun _ => ?_⟩
    · exact (hFc _ (hκK.mapsTo hw)).comp (hκc hw.2).continuousWithinAt hκK.mapsTo
    · exact hp.comp tendsto_I_mul_one_add_div_one_sub_nhdsWithin_closedBall_sdiff_one
  have hfd : DifferentiableOn ℂ (F ∘ κ) (ball 0 1) :=
    hFd.comp (fun w hw => (hasDerivAt_I_mul_one_add_div_one_sub
      (hball1 hw)).differentiableAt.differentiableWithinAt) hκH.mapsTo
  have hsub := subsingleton_sphere_fiber_of_isPreconnectedApproachAt one_pos hfd
    (hFi.comp hκH.injOn hκH.mapsTo) hGc (fun w hw => update_of_ne (hball1 hw) _ _)
    (by rwa [image_comp, hκH.image_eq])
  -- A real parameter `x` sits on the circle at its Cayley image, where the pulled-back map takes
  -- the value `F x`.
  have hreal (x : ℝ) (hx : F x = a) : ((x : ℂ) - Complex.I) / ((x : ℂ) + Complex.I) ∈
      {w | w ∈ sphere (0 : ℂ) 1 ∧ update (F ∘ κ) 1 p w = a} := by
    have hx0 : (0 : ℝ) ≤ (x : ℂ).im := by simp
    have hnorm := norm_sub_I_div_norm_add_I_ofReal x
    rw [← norm_div] at hnorm
    refine ⟨mem_sphere_zero_iff_norm.mpr hnorm, ?_⟩
    rw [update_of_ne (bijOn_sub_I_div_add_I_im_nonneg.mapsTo hx0).2, comp_apply]
    exact (congrArg F (I_mul_one_add_sub_I_div_add_I_div_one_sub
      (add_I_ne_zero_of_im_nonneg hx0))).trans hx
  intro x hx y hy
  exact_mod_cast injOn_sub_I_div_add_I (add_I_ne_zero_of_im_nonneg (by simp))
    (add_I_ne_zero_of_im_nonneg (by simp)) (hsub (hreal x hx) (hreal y hy))

end TauCeti
