/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
public import TauCeti.Analysis.Complex.Conformal.BoundaryCorrespondence
import TauCeti.Analysis.Complex.Conformal.ImageSimplyConnected
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

/-!
# Conformal maps of the closed upper half-plane

This file transports a conformal map of the closed unit disc to the closed upper half-plane.
The Cayley transform followed by a rotation identifies the closed upper half-plane with the closed
disc minus a specified boundary point, so the transported map has that boundary value as its limit
at infinity.

## Main statements

* TauCeti.bijOn_mul_left_of_norm_eq_one: multiplication by a unit complex number preserves the
  open unit disc and carries the closed unit disc with 1 removed to the disc with that number
  removed.
* TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_injOn_closedBall: transport of a
  continuous injective closed-disc map which is holomorphic on the open disc.
-/

public section

open Bornology Complex Filter Metric Set Topology

namespace TauCeti

/-- Multiplication by a unit complex number maps the closed unit disc with 1 removed
bijectively onto the closed unit disc with that number removed, and the open unit disc
onto itself. -/
theorem bijOn_mul_left_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    BijOn (ζ * ·) (closedBall 0 1 \ {1}) (closedBall 0 1 \ {ζ}) ∧
      BijOn (ζ * ·) (ball 0 1) (ball 0 1) := by
  have hζ0 : ζ ≠ 0 := norm_ne_zero_iff.mp (hζ ▸ one_ne_zero)
  have hinj : Function.Injective (ζ * ·) := mul_right_injective₀ hζ0
  have hball : (ζ * ·) '' ball (0 : ℂ) 1 = ball 0 1 := by
    simpa [hζ] using (image_smul (a := ζ) (t := ball (0 : ℂ) 1)).trans (smul_ball hζ0 0 1)
  have hclosed : (ζ * ·) '' closedBall (0 : ℂ) 1 = closedBall 0 1 := by
    simpa [hζ] using (image_smul (a := ζ) (t := closedBall (0 : ℂ) 1)).trans
      (smul_closedBall' hζ0 0 1)
  have hH := hinj.injOn.bijOn_image (s := ball (0 : ℂ) 1)
  have hK := hinj.injOn.bijOn_image (s := closedBall (0 : ℂ) 1 \ {1})
  rw [hball] at hH
  rw [image_sdiff hinj, hclosed, image_singleton, mul_one] at hK
  exact ⟨hK, hH⟩

/-- A conformal map of the closed disc can be transported to the closed upper half-plane.
Let g be continuous and injective on the closed unit disc and holomorphic on the open disc, with
g applied to the open disc equal to Ω, and let p lie in the frontier of Ω. Then precomposing g
with a rotated Cayley transform gives a map which is continuous on the closed upper half-plane,
holomorphic on the open upper half-plane, and has the stated bijectivity and limit properties. -/
theorem exists_continuousOn_bijOn_upperHalfPlaneSet_of_injOn_closedBall {g : ℂ → ℂ} {Ω : Set ℂ}
    (hgc : ContinuousOn g (closedBall 0 1)) (hgd : DifferentiableOn ℂ g (ball 0 1))
    (hgi : InjOn g (closedBall 0 1)) (hgΩ : g '' ball 0 1 = Ω) {p : ℂ} (hp : p ∈ frontier Ω) :
    ∃ f : ℂ → ℂ, ContinuousOn f {z | 0 ≤ z.im} ∧
      DifferentiableOn ℂ f UpperHalfPlane.upperHalfPlaneSet ∧
      BijOn f UpperHalfPlane.upperHalfPlaneSet Ω ∧ BijOn f {z | 0 ≤ z.im} (closure Ω \ {p}) ∧
      BijOn f {z | z.im = 0} (frontier Ω \ {p}) ∧
      Tendsto f (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝 p) := by
  have hgi' : InjOn g (ball 0 1) := hgi.mono ball_subset_closedBall
  have hΩo : IsOpen Ω := hgΩ ▸ isOpen_image_of_differentiableOn_of_injOn isOpen_ball hgd hgi'
  have hcl : closure (ball (0 : ℂ) 1) = closedBall 0 1 := closure_ball 0 one_ne_zero
  have hgimg : g '' closedBall 0 1 = closure Ω := by
    rw [← hcl, image_closure_eq_closure_image isBounded_ball (hcl ▸ hgc) (fun _ _ => rfl), hgΩ]
  obtain ⟨ζ, hζ, rfl⟩ : p ∈ g '' closedBall 0 1 := hgimg ▸ frontier_subset_closure hp
  have hζ1 : ‖ζ‖ = 1 := by
    refine le_antisymm (mem_closedBall_zero_iff.mp hζ) (not_lt.mp fun hlt => ?_)
    exact (disjoint_frontier_iff_isOpen.mpr hΩo).notMem_of_mem_left hp
      (hgΩ ▸ mem_image_of_mem g (mem_ball_zero_iff.mpr hlt))
  obtain ⟨hrotK, hrotH⟩ := bijOn_mul_left_of_norm_eq_one hζ1
  set c : ℂ → ℂ := fun z => ζ * ((z - I) / (z + I))
  have hcH : BijOn c UpperHalfPlane.upperHalfPlaneSet (ball 0 1) :=
    hrotH.comp bijOn_sub_I_div_add_I_upperHalfPlaneSet
  have hcK : BijOn c {z | 0 ≤ z.im} (closedBall 0 1 \ {ζ}) :=
    hrotK.comp bijOn_sub_I_div_add_I_im_nonneg
  have hcd : DifferentiableOn ℂ c {z | 0 ≤ z.im} :=
    (differentiableOn_const ζ).mul differentiableOn_sub_I_div_add_I_im_nonneg
  have hct : Tendsto c (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝[closedBall 0 1] ζ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_inf_principal.mpr
      (Eventually.of_forall fun z hz => (hcK.mapsTo hz).1)⟩
    simpa using (tendsto_sub_I_div_add_I_cobounded.const_mul ζ).mono_left inf_le_left
  have hH : BijOn (g ∘ c) UpperHalfPlane.upperHalfPlaneSet Ω :=
    (hgΩ ▸ hgi'.bijOn_image).comp hcH
  have hK : BijOn (g ∘ c) {z | 0 ≤ z.im} (closure Ω \ {g ζ}) := by
    have h := (hgi.mono sdiff_subset).bijOn_image (s := closedBall (0 : ℂ) 1 \ {ζ})
    rw [hgi.image_sdiff_subset (singleton_subset_iff.mpr hζ), hgimg, image_singleton] at h
    exact h.comp hcK
  have hR : BijOn (g ∘ c) {z | z.im = 0} (frontier Ω \ {g ζ}) := by
    have hreal : {z : ℂ | z.im = 0} = {z | 0 ≤ z.im} \ UpperHalfPlane.upperHalfPlaneSet := by
      ext z
      simp only [Set.mem_sdiff, UpperHalfPlane.upperHalfPlaneSet, mem_ofPred_eq, not_lt]
      exact ⟨fun h => ⟨h.ge, h.le⟩, fun h => le_antisymm h.2 h.1⟩
    have h := (hK.injOn.mono (sdiff_subset (t := UpperHalfPlane.upperHalfPlaneSet))).bijOn_image
    rwa [hK.injOn.image_sdiff_subset (ofPred_subset_ofPred.mpr fun _ => le_of_lt), hK.image_eq,
      hH.image_eq, sdiff_right_comm, ← hΩo.frontier_eq, ← hreal] at h
  exact ⟨g ∘ c, hgc.comp hcd.continuousOn fun z hz => (hcK.mapsTo hz).1,
    hgd.comp (hcd.mono (ofPred_subset_ofPred.mpr fun _ => le_of_lt)) hcH.mapsTo, hH, hK, hR,
    (hgc ζ hζ).tendsto.comp hct⟩

end TauCeti
