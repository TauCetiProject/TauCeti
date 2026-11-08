/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Domain
import TauCeti.Analysis.Complex.Conformal.Jordan.Approach
import TauCeti.Analysis.Complex.PlaneSeparation.Inside
import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
import TauCeti.Analysis.Complex.Inversion
import TauCeti.Analysis.Normed.Field.Inversion
import TauCeti.Analysis.Normed.Module.FilledHull
import TauCeti.Topology.Separation.InvFunOn

/-!
# Carathéodory's theorem for both complementary domains of a Jordan curve

A Jordan curve `C ⊆ ℂ` has exactly two complementary components: its inside `filledHull C \ C`
and its outside `(filledHull C)ᶜ`. This file shows that the inside is a conformal image of the open
unit disc and the outside a conformal image of the exterior `(closedBall 0 1)ᶜ` of the closed unit
disc, and that these maps extend to homeomorphisms of the closed disc onto `filledHull C`, the
closure of the inside, and of the closed exterior `(ball 0 1)ᶜ` onto `(filledHull C \ C)ᶜ`, the
closure of the outside, the unit circle going onto `C` in both cases.

* For the inside, the closed unit disc is homeomorphic to `filledHull C`, the closure of the inside,
  by a map that is holomorphic on the open disc and sends its centre to any prescribed point of the
  inside. This is Carathéodory's theorem for the Jordan domain `filledHull C \ C`, and in
  particular the closed-disc form of the Schoenflies theorem.
* For the outside, the closed exterior `(ball 0 1)ᶜ` of the unit disc is homeomorphic to
  `(filledHull C \ C)ᶜ`, the closure of the outside, by a map that is holomorphic off the closed
  disc and tends to infinity at infinity. Inverting the outside about a point `p` of the inside,
  `z ↦ (z - p)⁻¹`, and adding `0`, the image of infinity, gives a bounded Jordan domain bounded by
  the inverted curve
  (`TauCeti.IsJordanCurve.isJordanDomain_insert_zero_image_inv_sub_compl_filledHull`); the
  exterior map is read back from its Riemann map normalized at `0`.

## Main results

* `TauCeti.IsJordanCurve.exists_homeomorph_closedBall_filledHull` — the inside of a Jordan curve
  is the image of the disc under a holomorphic bijection that extends to a homeomorphism of the
  closed disc onto `filledHull C`, carrying the circle onto `C`.
* `TauCeti.IsJordanCurve.exists_homeomorph_compl_ball_compl_filledHull_sdiff` — the outside of a
  Jordan curve is the image of the exterior of the disc under a holomorphic bijection that tends to
  infinity at infinity and extends to a homeomorphism of the closed exterior onto the complement
  of the inside, carrying the circle onto `C`.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Theorem 2.6.
-/

public section

open Bornology Filter Function Metric Set Topology

namespace TauCeti

variable {C : Set ℂ} {p : ℂ}

/-! ## The inside -/

/-- **Carathéodory's theorem for the inside of a Jordan curve.** For a Jordan curve `C ⊆ ℂ` and a
point `p` of its inside `filledHull C \ C`, there is a map `g`, holomorphic on the open unit disc
with `g 0 = p`, carrying the disc bijectively onto the inside and the unit circle bijectively onto
`C`, which restricts to a homeomorphism of the closed disc onto `filledHull C`. -/
theorem IsJordanCurve.exists_homeomorph_closedBall_filledHull (hC : IsJordanCurve C)
    (hp : p ∈ filledHull C \ C) :
    ∃ g : ℂ → ℂ, ContinuousOn g (closedBall 0 1) ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn g (ball 0 1) (filledHull C \ C) ∧ BijOn g (sphere 0 1) C ∧ g 0 = p ∧
      ∃ e : closedBall (0 : ℂ) 1 ≃ₜ filledHull C,
        ∀ z : closedBall (0 : ℂ) 1, (e z : ℂ) = g z := by
  have hJ := hC.isJordanDomain_filledHull_sdiff
  obtain ⟨g, hgc, hgd, hgbij, hg0, e, he⟩ :=
    exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier_of_mem hJ.isOpen
      hJ.isConnected hJ.isBounded hJ.isJordanCurve_frontier hp
  have hgS := bijOn_sphere_frontier hgc hgd (injOn_closedBall_of_homeomorph_closure e he) hgbij
  exact ⟨g, hgc, hgd, hgbij, hC.frontier_filledHull_sdiff ▸ hgS, hg0,
    e.trans (Homeomorph.setCongr hC.closure_filledHull_sdiff), he⟩

/-! ## The outside -/

/-- **Carathéodory's theorem for the outside of a Jordan curve.** For a Jordan curve `C ⊆ ℂ` there
is a map `h`, holomorphic off the closed unit disc and tending to infinity at infinity, carrying the
exterior of the closed disc bijectively onto the outside `(filledHull C)ᶜ` and the unit circle
bijectively onto `C`, which restricts to a homeomorphism of the closed exterior `(ball 0 1)ᶜ` onto
the complement of the inside, the closure of the outside
(`TauCeti.IsJordanCurve.closure_compl_filledHull`). -/
theorem IsJordanCurve.exists_homeomorph_compl_ball_compl_filledHull_sdiff (hC : IsJordanCurve C) :
    ∃ h : ℂ → ℂ, ContinuousOn h (ball 0 1)ᶜ ∧ DifferentiableOn ℂ h (closedBall 0 1)ᶜ ∧
      BijOn h (closedBall 0 1)ᶜ (filledHull C)ᶜ ∧ BijOn h (sphere 0 1) C ∧
      Tendsto h (cobounded ℂ) (cobounded ℂ) ∧
      ∃ e : ((ball (0 : ℂ) 1)ᶜ : Set ℂ) ≃ₜ ((filledHull C \ C)ᶜ : Set ℂ),
        ∀ z : ((ball (0 : ℂ) 1)ᶜ : Set ℂ), (e z : ℂ) = h z := by
  -- Invert the outside about a point `p` of the inside, take the Riemann map `G` of the resulting
  -- Jordan domain `W` normalized by `G 0 = 0`, and read it back: `h w = p + (G w⁻¹)⁻¹`.
  obtain ⟨p, hp⟩ := hC.nonempty_filledHull_sdiff
  have hJ := hC.isJordanDomain_insert_zero_image_inv_sub_compl_filledHull hp
  set W := insert 0 ((fun z : ℂ => (z - p)⁻¹) '' (filledHull C)ᶜ) with hW
  obtain ⟨G, hGc, hGd, hGbij, hG0, E, hE⟩ :=
    exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier_of_mem hJ.isOpen
      hJ.isConnected hJ.isBounded hJ.isJordanCurve_frontier (mem_insert 0 _)
  have h0 {S : Set ℂ} (hS : p ∉ S) : (0 : ℂ) ∉ (fun z : ℂ => (z - p)⁻¹) '' S := by
    rintro ⟨z, hz, hz0⟩
    rw [inv_eq_zero, sub_eq_zero] at hz0
    exact hS (hz0 ▸ hz)
  /- The pieces of `W` and of its closure, away from `0`, are the inverted pieces of the closed
  outside. -/
  have hclW : closure W \ {0} = (fun z : ℂ => (z - p)⁻¹) '' (filledHull C \ C)ᶜ := by
    rw [hW, closure_insert_zero_image_inv_sub, hC.closure_compl_filledHull,
      insert_sdiff_self_of_notMem (h0 (not_not_intro hp))]
  have hW0 : W \ {0} = (fun z : ℂ => (z - p)⁻¹) '' (filledHull C)ᶜ :=
    insert_sdiff_self_of_notMem (h0 fun h => h hp.1)
  /- The extension `G` is a bijection of the closed disc onto `closure W`, and of the circle onto
  `frontier W`. -/
  have hGi := injOn_closedBall_of_homeomorph_closure E hE
  have hGcl := bijOn_closedBall_closure hGc hGi hGbij
  have hGS := bijOn_sphere_frontier hGc hGd hGi hGbij
  rw [hC.frontier_insert_zero_image_inv_sub_compl_filledHull hp] at hGS
  have hG2 : BijOn G (ball 0 1 \ {0}) (W \ {0}) := by
    simpa only [hG0] using hGbij.sdiff_singleton (mem_ball_self one_pos)
  have hne : ∀ x ∈ ball (0 : ℂ) 1, x ≠ 0 → G x ≠ 0 := fun x hx hx0 => (hG2.mapsTo ⟨hx, hx0⟩).2
  have hGinvc : ContinuousOn (invFunOn G (closedBall 0 1)) (closure W) :=
    hGcl.image_eq ▸ hGc.continuousOn_invFunOn_image_of_isCompact (isCompact_closedBall 0 1)
      subset_rfl hGcl.injOn (by simp)
  obtain ⟨hhc, e, he⟩ := exists_homeomorph_compl_ball_add_inv_comp_inv
    (not_not_intro hp) hG0 hGc hGcl hGinvc hclW
  refine ⟨_, hhc, differentiableOn_add_inv_comp_inv p hGd hne,
    (bijOn_add_inv_image_inv_sub _).comp ((hW0 ▸ hG2).comp bijOn_inv_compl_closedBall_one),
    (bijOn_add_inv_image_inv_sub _).comp (hGS.comp bijOn_inv_sphere_one),
    tendsto_add_inv_comp_inv p
      (hGd.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self one_pos))) hG0 hne, e, he⟩

end TauCeti
