/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.PolygonalDomain

import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.BoundaryPrevertex
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.HalfStripExteriorEnd
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.LocalBoundary
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.ParallelEnd
import TauCeti.Analysis.Complex.Conformal.Jordan.Unbounded.SectorEnd
import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Converse

/-!
# Conformal maps onto polygonal domains with several vertices at infinity

A polygonal domain `U` may reach infinity along several ends, as a strip does.  A conformal map
`f` of the upper half-plane onto `U` then tends to infinity at several real boundary parameters,
so it has no continuous extension to the closed upper half-plane.  Its inverted coordinate
`g = (f - q)⁻¹` can still be continuous there.  The real zeros of `g` are the prevertices of the
vertices at infinity, and away from them the recovered map `z ↦ q + (g z)⁻¹` is a continuous
finite boundary extension of `f`.

This file shows that such an `f` is an affine image of the Schwarz--Christoffel primitive whose
prevertices are the prevertices `a i` of the finite vertices together with the zeros `d k` of
`g`.  The domain is described by its local geometry, as in
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain`: an open half-plane
near each frontier point other than the vertices `v i`, and an open sector of opening
`(e i + 1) * π` near `v i`.  Near the zero `d k` the map `f` takes its values in one model end
lying in `U`, with turning exponent `e' k`:

* the far part of a sector of opening `β * π`, `0 < β < 2`, where `e' k = -β - 1`;
* the far part of a half-strip between two parallel sides, where `e' k = -1`;
* the far part of the exterior of a closed half-strip, an end of opening `2 * π`, where
  `e' k = -3`.

The point at infinity of the upper half-plane is assumed to go to a point on a side of `U`.  Then
all the exponents sum to `-2`.

These hypotheses are what a Riemann map of such a domain, in the inverted coordinate of
`TauCeti.exists_bijOn_upperHalfPlaneSet_of_locallyConnectedSpace_frontier_image_inv_sub`, provides
once the point at infinity of the half-plane is moved to a side; that normalization, and matching
each zero with its end, are not carried out here.

## Main results

* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_inverted_coordinate` -- a conformal
  map onto a polygonal domain with several vertices at infinity is an affine image of the
  Schwarz--Christoffel primitive.
* `TauCeti.exponent_sum_eq_neg_two_of_inverted_coordinate` -- its turning exponents, finite and
  at infinity, sum to `-2`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {ι κ : Type*} {U : Set ℂ} {f g : ℂ → ℂ} {q ζ : ℂ} {v : ι → ℂ}

/-- The local boundary data of the Schwarz--Christoffel formula for the recovered map
`z ↦ q + (g z)⁻¹`, together with the limit `-2` of its `z * F''(z) / F'(z)` at infinity. -/
private theorem eqOn_and_tendsto_of_inverted_coordinate [Fintype ι] [Fintype κ]
    (a e : ι → ℝ) (ha : Injective a) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    (d e' : κ → ℝ) (hd : Injective d) (z₀ : UpperHalfPlane)
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hfU : f '' upperHalfPlaneSet = U) (hga : ∀ i, g (a i) ≠ 0) (hgv : ∀ i, q + (g (a i))⁻¹ = v i)
    (hdz : ∀ k, g (d k) = 0) (hzd : ∀ x : ℝ, g x = 0 → ∃ k, d k = x)
    (hζ : Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 ζ)) (hζ0 : ζ ≠ 0)
    (hζg : ζ ∉ g '' {z : ℂ | 0 ≤ z.im})
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hend : ∀ k,
      (e' k ∈ Ioo (-3 : ℝ) (-1) ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < (-e' k - 1) * Real.pi / 2} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ),
          f z ∈ {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < (-e' k - 1) * Real.pi / 2}) ∨
      (e' k = -1 ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ),
          f z ∈ {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi}) ∨
      (e' k = -3 ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ), f z ∈
          {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)})) :
    EqOn (fun z => q + (g z)⁻¹) (fun z =>
        deriv (fun z => q + (g z)⁻¹) z₀ /
          schwarzChristoffelIntegrand (Sum.elim a d) (Sum.elim e e') z₀ *
        schwarzChristoffelPrimitive (Sum.elim a d) (Sum.elim e e') z₀ z + (q + (g z₀)⁻¹))
      upperHalfPlaneSet ∧
    Tendsto (fun z => z * logDeriv (deriv (fun z => q + (g z)⁻¹)) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-2)) := by
  set F : ℂ → ℂ := fun z => q + (g z)⁻¹
  set T : Set ℂ := {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0}
  have hHT : upperHalfPlaneSet ⊆ T := fun z hz => ⟨le_of_lt hz, hgne z hz⟩
  have hFf : EqOn F f upperHalfPlaneSet := fun z hz =>
    (eq_add_inv_of_inverted_coordinate hgf hz).symm
  have hFU : F '' upperHalfPlaneSet = U := (hFf.image_eq).trans hfU
  have hFd : DifferentiableOn ℂ F upperHalfPlaneSet :=
    (differentiableOn_const q).add (hgd.inv hgne)
  have hFc : ContinuousOn F T :=
    continuousOn_const.add ((hgc.mono fun (_ : ℂ) (hz : _ ∈ T) => hz.1).inv₀ fun _ hz => hz.2)
  have hFi : InjOn F T := fun z hz z' hz' h =>
    hgi hz hz' (inv_injective (add_left_cancel h))
  have hFn : ∀ z ∈ upperHalfPlaneSet, deriv F z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn hFd isOpen_upperHalfPlaneSet (hFi.mono hHT) hz
  -- the boundary values of `F` where `g` is nonzero are the values of `g` there, inverted
  have hFeq {z z' : ℂ} (h : F z = F z') : g z = g z' := inv_injective (add_left_cancel h)
  have hS {S : Set ℂ} (h : S ⊆ U) : S ⊆ f '' upperHalfPlaneSet := hfU ▸ h
  -- the point at infinity of the half-plane is carried to a side
  have hinfty : Tendsto (fun z => z * logDeriv (deriv F) z) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
      (𝓝 (-2)) := by
    refine tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_tendsto_of_side (v := v) hFd hHT
      (hζ.eventually (eventually_ne_nhds hζ0) |>.and (eventually_inf_principal.mpr
        (Eventually.of_forall fun _ hz => hz)) |>.mono fun _ h => ⟨h.2, h.1⟩) hFc hFi hFU
      (tendsto_const_nhds.add (hζ.inv₀ hζ0)) ?_ (fun i h => ?_) hside
    · rintro ⟨z, hz, h⟩
      exact hζg ⟨z, hz.1, inv_inj.mp (add_left_cancel h)⟩
    · rw [← hgv i] at h
      exact hζg ⟨a i, by simp, (inv_inj.mp (add_left_cancel h)).symm⟩
  refine ⟨eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary (Sum.elim a d)
    (Sum.elim e e') (ha.sumElim hd fun i k h => hga i (by rw [h]; exact hdz k)) z₀ hFd hFn
    (fun x hx => ?_) ?_ hinfty, hinfty⟩
  · -- a real point that is not a prevertex is carried to a side
    have hx0 : g x ≠ 0 := fun h => by
      obtain ⟨k, rfl⟩ := hzd x h
      exact hx (Sum.inr k) rfl
    have hxU : F x ∈ frontier U := hFU ▸
      mem_frontier_image_upperHalfPlaneSet_of_mem_of_im_eq_zero hHT (hFc _ ⟨by simp, hx0⟩) hFi
        ⟨by simp, hx0⟩ (ofReal_im x)
    have hxv : ∀ i, F x ≠ v i := fun i h => by
      rw [← hgv i] at h
      exact hx (Sum.inl i) (ofReal_injective (hgi ⟨by simp, hga i⟩ ⟨by simp, hx0⟩ (hFeq h).symm))
    obtain ⟨ρ, hρ, p, b, hb, hU⟩ := hside _ hxU hxv
    obtain ⟨r, hr, hcont, hinj, hreal, hupper⟩ :=
      exists_ball_side_of_inverted_coordinate hgc hgi hFU hx0 hρ hU
    exact ⟨r, hr, p, b, hb, hcont, hinj, hreal, hupper⟩
  · rintro (i | k)
    · -- the prevertex `a i` is carried to the vertex `v i`
      obtain ⟨ρ, hρ, b, hb, hU⟩ := hcorner i
      rw [← hgv i] at hU
      obtain ⟨r, hr, hcont, hinj, hupper, hreal⟩ :=
        exists_ball_corner_of_inverted_coordinate hgc hgi hFU (hga i) hρ hb hU
      exact Or.inl ⟨he i, r, hr, b, hb, hcont, hinj, hupper, hreal⟩
    · -- the zero `d k` is carried to the vertex at infinity of the end it lands in
      rcases hend k with ⟨hek, ρ, c, b, hb, hSU, hfS⟩ | ⟨hek, ρ, c, b, hb, hSU, hfS⟩ |
        ⟨hek, ρ, c, b, hb, hSU, hfS⟩
      · obtain ⟨r, hr, hG, hG0, hGc, hGi, hupper, hreal⟩ :=
          exists_ball_sector_end_of_inverted_coordinate hgc hgd hgf hgne hgi (hdz k)
            (β := -e' k - 1) ⟨by linarith [hek.2], by linarith [hek.1]⟩ hb (hS hSU) hfS
        refine Or.inr (Or.inl ⟨hek, r, hr, c, b, hb, _, fun z hz => ?_, hG0, hGc, hGi, hupper,
          hreal⟩)
        simp only [hG hz, hFf hz.2]
      · obtain ⟨r, hr, c', b', hb', G, hG, hG0, hGc, hGr, hGu, hGi⟩ :=
          exists_ball_halfStrip_end_of_inverted_coordinate hgc hgd hgf hgne hgi (hdz k) hb
            (hS hSU) hfS
        refine Or.inr (Or.inr (Or.inl ⟨hek, r, hr, c', b', hb', G, fun z hz => ?_, hG0, hGc, hGr,
          hGu, hGi⟩))
        simp only [hG hz, hFf hz.2]
      · obtain ⟨r, hr, ρ', hFc', hFi', hFt, hFS⟩ :=
          exists_ball_halfStripExterior_end_of_inverted_coordinate hgc hgd hgf hgne hgi (hdz k) hb
            (hS hSU) hfS
        exact Or.inr (Or.inr (Or.inr ⟨hek, r, hr, ρ', c, b, hb, hFc', hFi', hFt, hFS⟩))

/-- **The Schwarz--Christoffel formula for a polygonal domain with several vertices at infinity.**
Let `f` be a holomorphic map of the upper half-plane onto `U`, and let its inverted coordinate
`g = (f - q)⁻¹` extend continuously to the closed upper half-plane, nonvanishing in the open
half-plane and injective off its zeros.  Suppose that:
* `U` coincides with an open half-plane near each frontier point other than the vertices `v i`,
  and with the open sector of opening `(e i + 1) * π` near `v i`, where `e i ∈ (-1, 1)`; the
  prevertex `a i` of `v i` is a real point with `g (a i) ≠ 0` and `q + (g (a i))⁻¹ = v i`;
* the real zeros of `g` are the distinct points `d k`, and near `d k` the map `f` takes its values
  in the far part, contained in `U`, of a sector of opening `β * π` with `e' k = -β - 1 ∈ (-3, -1)`,
  of a half-strip with `e' k = -1`, or of the exterior of a closed half-strip with `e' k = -3`;
* at infinity `g` tends to a nonzero limit `ζ` which is not one of its values on the closed upper
  half-plane: the point at infinity of the half-plane is carried to the point `q + ζ⁻¹` on a side
  of `U`.

Then throughout the upper half-plane

`f z = (f'(z₀) / integrand(z₀)) * F z + f z₀`,

where `F` is the normalized Schwarz--Christoffel primitive whose prevertices are the `a i` and the
`d k` and whose turning exponents are the `e i` and the `e' k`. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_inverted_coordinate [Fintype ι]
    [Fintype κ] (a e : ι → ℝ) (ha : Injective a) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    (d e' : κ → ℝ) (hd : Injective d) (z₀ : UpperHalfPlane)
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hfU : f '' upperHalfPlaneSet = U) (hga : ∀ i, g (a i) ≠ 0) (hgv : ∀ i, q + (g (a i))⁻¹ = v i)
    (hdz : ∀ k, g (d k) = 0) (hzd : ∀ x : ℝ, g x = 0 → ∃ k, d k = x)
    (hζ : Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 ζ)) (hζ0 : ζ ≠ 0)
    (hζg : ζ ∉ g '' {z : ℂ | 0 ≤ z.im})
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hend : ∀ k,
      (e' k ∈ Ioo (-3 : ℝ) (-1) ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < (-e' k - 1) * Real.pi / 2} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ),
          f z ∈ {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < (-e' k - 1) * Real.pi / 2}) ∨
      (e' k = -1 ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ),
          f z ∈ {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi}) ∨
      (e' k = -3 ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ), f z ∈
          {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)})) :
    EqOn f (fun z => deriv f z₀ / schwarzChristoffelIntegrand (Sum.elim a d) (Sum.elim e e') z₀ *
      schwarzChristoffelPrimitive (Sum.elim a d) (Sum.elim e e') z₀ z + f z₀)
      upperHalfPlaneSet := by
  have hFf : EqOn (fun z => q + (g z)⁻¹) f upperHalfPlaneSet := fun z hz =>
    (eq_add_inv_of_inverted_coordinate hgf hz).symm
  have hF := hFf.eventuallyEq_of_mem (isOpen_upperHalfPlaneSet.mem_nhds z₀.im_pos)
  intro z hz
  rw [← hFf hz, ← hF.deriv_eq, ← hFf z₀.im_pos]
  exact (eqOn_and_tendsto_of_inverted_coordinate a e ha he d e' hd z₀ hgc hgd hgf hgne hgi hfU hga
    hgv hdz hzd hζ hζ0 hζg hside hcorner hend).1 hz

/-- **The angle sum of a polygonal domain with several vertices at infinity.**  Under the hypotheses
of `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_inverted_coordinate`, the turning
exponents `e i` of the finite vertices and `e' k` of the vertices at infinity sum to `-2`.  For a
strip, for instance, the two parallel-sided ends have `e' k = -1`. -/
theorem exponent_sum_eq_neg_two_of_inverted_coordinate [Fintype ι] [Fintype κ]
    (a e : ι → ℝ) (ha : Injective a) (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1)
    (d e' : κ → ℝ) (hd : Injective d)
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im}) (hgd : DifferentiableOn ℂ g upperHalfPlaneSet)
    (hgf : EqOn g (fun z => (f z - q)⁻¹) upperHalfPlaneSet)
    (hgne : ∀ z ∈ upperHalfPlaneSet, g z ≠ 0) (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hfU : f '' upperHalfPlaneSet = U) (hga : ∀ i, g (a i) ≠ 0) (hgv : ∀ i, q + (g (a i))⁻¹ = v i)
    (hdz : ∀ k, g (d k) = 0) (hzd : ∀ x : ℝ, g x = 0 → ∃ k, d k = x)
    (hζ : Tendsto g (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 ζ)) (hζ0 : ζ ≠ 0)
    (hζg : ζ ∉ g '' {z : ℂ | 0 ≤ z.im})
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ p b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - p) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hend : ∀ k,
      (e' k ∈ Ioo (-3 : ℝ) (-1) ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < (-e' k - 1) * Real.pi / 2} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ),
          f z ∈ {w : ℂ | ρ < ‖w - c‖ ∧ |((w - c) / b).arg| < (-e' k - 1) * Real.pi / 2}) ∨
      (e' k = -1 ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ),
          f z ∈ {w : ℂ | ρ < ((w - c) / b).re ∧ ((w - c) / b).im ∈ Ioo 0 Real.pi}) ∨
      (e' k = -3 ∧ ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧
        {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)} ⊆ U ∧
        ∀ᶠ z in 𝓝[upperHalfPlaneSet] ((d k : ℝ) : ℂ), f z ∈
          {w : ℂ | ρ < ‖w - c‖ ∧ (((w - c) / b).re < 0 ∨ ((w - c) / b).im ∉ Icc 0 Real.pi)})) :
    ∑ i, e i + ∑ k, e' k = -2 := by
  set F : ℂ → ℂ := fun z => q + (g z)⁻¹
  have hFd : DifferentiableOn ℂ F upperHalfPlaneSet :=
    (differentiableOn_const q).add (hgd.inv hgne)
  have hFn : ∀ z ∈ upperHalfPlaneSet, deriv F z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn hFd isOpen_upperHalfPlaneSet
      (fun z hz z' hz' h => hgi ⟨le_of_lt hz, hgne z hz⟩ ⟨le_of_lt hz', hgne z' hz'⟩
        (inv_injective (add_left_cancel h))) hz
  obtain ⟨hform, hinfty⟩ := eqOn_and_tendsto_of_inverted_coordinate a e ha he d e' hd
    UpperHalfPlane.I hgc hgd hgf hgne hgi hfU hga hgv hdz hzd hζ hζ0 hζg hside hcorner hend
  -- `F` is an affine image of the primitive, so its pre-Schwarzian is the partial-fraction sum
  have hpre := (exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_iff (Sum.elim a d)
    (Sum.elim e e') UpperHalfPlane.I hFd hFn).mp ⟨_, div_ne_zero (hFn _ UpperHalfPlane.I.im_pos)
      (schwarzChristoffelIntegrand_ne_zero _ _ UpperHalfPlane.I.im_pos), _, hform⟩
  have hsum := exponent_sum_eq_of_logDeriv_deriv_eqOn (fun j => ((Sum.elim a d j : ℝ) : ℂ))
    (fun j => ((Sum.elim e e' j : ℝ) : ℂ)) hpre hinfty
  rw [Fintype.sum_sum_type] at hsum
  exact_mod_cast hsum

end TauCeti

end
