/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.UpperHalfPlane
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

import TauCeti.Analysis.Complex.Conformal.Caratheodory

/-!
# Upper-half-plane maps with locally connected boundary

Carathéodory's continuity theorem extends a Riemann map to the closed disc when the target has
locally connected boundary, but the extension need not be injective there.  This file transports
that extension to the closed upper half-plane while retaining the exact interior bijection and the
boundary correspondence.

The boundary point omitted by the Cayley transform is the limit at infinity.  Other points of the
source circle can have the same boundary value, so the finite real boundary values cover the target
frontier up to that distinguished point rather than necessarily omitting it.

## Main statement

* `TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_continuousOn_closedBall` -- transport
  of a continuous closed-disc extension without a boundary-injectivity hypothesis.
* `TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier` -- a
  Riemann map of a bounded simply connected domain with locally connected boundary, transported to
  the upper half-plane with a prescribed boundary limit at infinity.

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
    refine Subset.antisymm ?_ ?_
    · rintro w (rfl | ⟨z, hz, rfl⟩)
      · exact frontier_subset_closure hp
      · exact hgcl ▸ mem_image_of_mem g (hcK.mapsTo hz).1
    · intro w hw
      obtain ⟨x, hx, hxw⟩ := hgcl.symm.subset hw
      by_cases hxζ : x = ζ
      · exact mem_insert_iff.mpr (Or.inl (hxw.symm.trans ((congrArg g hxζ).trans hζp)))
      · obtain ⟨z, hz, hzx⟩ := hcK.surjOn ⟨hx, hxζ⟩
        exact mem_insert_iff.mpr
          (Or.inr ⟨z, hz, by simpa [Function.comp_def, hzx] using hxw⟩)
  have hR : insert p ((g ∘ c) '' {z : ℂ | z.im = 0}) = frontier Ω := by
    refine Subset.antisymm ?_ ?_
    · rintro w (rfl | ⟨z, hz, rfl⟩)
      · exact hp
      · exact hgfr ▸ mem_image_of_mem g (hcR.mapsTo hz).1
    · intro w hw
      obtain ⟨x, hx, hxw⟩ := hgfr.symm.subset hw
      by_cases hxζ : x = ζ
      · exact mem_insert_iff.mpr (Or.inl (hxw.symm.trans ((congrArg g hxζ).trans hζp)))
      · obtain ⟨z, hz, hzx⟩ := hcR.surjOn ⟨hx, hxζ⟩
        exact mem_insert_iff.mpr
          (Or.inr ⟨z, hz, by simpa [Function.comp_def, hzx] using hxw⟩)
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

end TauCeti
