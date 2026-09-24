/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.Jordan.Approach
public import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley
import TauCeti.Analysis.Complex.Conformal.Caratheodory

/-!
# The Riemann map of a Jordan domain on the closed upper half-plane

Carathéodory's theorem, in the form
`TauCeti.exists_homeomorph_closedBall_closure_of_isJordanCurve_frontier`, extends the Riemann map
of a Jordan domain `Ω` to a homeomorphism from the closed unit disc onto `closure Ω`. Many
boundary-value constructions, the Schwarz–Christoffel formula among them, are instead phrased on
the closed upper half-plane, whose boundary is the real line together with the point at infinity.
This file transports Carathéodory's theorem there.

Composing the disc map with a rotation of the Cayley transform `z ↦ (z - i) / (z + i)`
(`TauCeti.bijOn_sub_I_div_add_I_im_nonneg`) gives, for any prescribed boundary point `p` of `Ω`, a
map `f` that is continuous on the closed upper half-plane, holomorphic on the open one, a bijection
from the open half-plane onto `Ω`, from the closed half-plane onto `closure Ω \ {p}` and from the
real line onto `frontier Ω \ {p}`, and tends to `p` at infinity: the point at infinity closes up
the boundary curve at `p`.

## Main statements

* `TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_injOn_closedBall`: a map continuous and
  injective on the closed unit disc and holomorphic inside it, transported to the closed upper
  half-plane with `∞` sent to a prescribed boundary point.
* `TauCeti.exists_continuousOn_bijOn_upperHalfPlaneSet_of_isJordanCurve_frontier`: the Riemann
  map of a Jordan domain, normalized to send `∞` to a prescribed boundary point, as a continuous
  injection of the closed upper half-plane.

## References

* C. Carathéodory, *Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung*,
  Math. Ann. **73** (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Bornology Complex Filter Metric Set Topology

namespace TauCeti

/-- Multiplication by a unit complex number `ζ` maps the closed unit disc with `1` removed
bijectively onto the closed unit disc with `ζ` removed, and the open unit disc onto itself. -/
private theorem bijOn_mul_left_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
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

/-- **A conformal map of the closed disc, on the closed upper half-plane.** Let `g` be continuous
and injective on the closed unit disc and holomorphic on the open disc, with `g '' ball 0 1 = Ω`,
and let `p` be a point of `frontier Ω`. Then precomposing `g` with a rotated Cayley transform gives
a map `f` which is continuous on the closed upper half-plane, holomorphic on the open upper
half-plane, a bijection from the open upper half-plane onto `Ω`, from the closed upper half-plane
onto `closure Ω \ {p}` and from the real line onto `frontier Ω \ {p}`, and which tends to `p` at
infinity within the closed half-plane. -/
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
  -- The prescribed boundary point is the value of `g` at a point `ζ` of the unit circle.
  obtain ⟨ζ, hζ, rfl⟩ : p ∈ g '' closedBall 0 1 := hgimg ▸ frontier_subset_closure hp
  have hζ1 : ‖ζ‖ = 1 := by
    refine le_antisymm (mem_closedBall_zero_iff.mp hζ) (not_lt.mp fun hlt => ?_)
    exact (disjoint_frontier_iff_isOpen.mpr hΩo).notMem_of_mem_left hp
      (hgΩ ▸ mem_image_of_mem g (mem_ball_zero_iff.mpr hlt))
  obtain ⟨hrotK, hrotH⟩ := bijOn_mul_left_of_norm_eq_one hζ1
  -- The rotated Cayley transform `c`, sending `∞` to `ζ`.
  set c : ℂ → ℂ := fun z => ζ * ((z - I) / (z + I))
  have hcH : BijOn c UpperHalfPlane.upperHalfPlaneSet (ball 0 1) :=
    hrotH.comp bijOn_sub_I_div_add_I_upperHalfPlaneSet
  have hcK : BijOn c {z | 0 ≤ z.im} (closedBall 0 1 \ {ζ}) :=
    hrotK.comp bijOn_sub_I_div_add_I_im_nonneg
  have hcd : DifferentiableOn ℂ c {z | 0 ≤ z.im} :=
    (differentiableOn_const ζ).mul differentiableOn_sub_I_div_add_I_im_nonneg
  -- `c` tends to `ζ` at infinity inside the closed disc, where `g` is continuous.
  have hct : Tendsto c (cobounded ℂ ⊓ 𝓟 {z | 0 ≤ z.im}) (𝓝[closedBall 0 1] ζ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, eventually_inf_principal.mpr
      (Eventually.of_forall fun z hz => (hcK.mapsTo hz).1)⟩
    simpa using (tendsto_sub_I_div_add_I_cobounded.const_mul ζ).mono_left inf_le_left
  have hH : BijOn (g ∘ c) UpperHalfPlane.upperHalfPlaneSet Ω :=
    (hgΩ ▸ hgi'.bijOn_image).comp hcH
  have hK : BijOn (g ∘ c) {z | 0 ≤ z.im} (closure Ω \ {g ζ}) := by
    have h := (hgi.mono sdiff_subset).bijOn_image (s := closedBall 0 1 \ {ζ})
    rw [hgi.image_sdiff_subset (singleton_subset_iff.mpr hζ), hgimg, image_singleton] at h
    exact h.comp hcK
  -- The real line is the closed half-plane minus the open one, so its image is
  -- `(closure Ω \ {g ζ}) \ Ω = frontier Ω \ {g ζ}`.
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

/-- **Carathéodory's theorem on the closed upper half-plane.** Let `Ω` be a bounded, simply
connected open subset of `ℂ` whose frontier is a Jordan curve, and let `p` be a point of that
frontier. Then there is a map `f` which is continuous on the closed upper half-plane, holomorphic on
the open upper half-plane, a bijection from the open upper half-plane onto `Ω`, from the closed
upper half-plane onto `closure Ω \ {p}` and from the real line onto `frontier Ω \ {p}`, and which
tends to `p` at infinity within the closed half-plane. -/
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
