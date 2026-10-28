/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.LocalFrontier
public import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Finite boundary geometry from an inverted coordinate

A conformal map onto an unbounded domain can have several accesses to infinity, so the map itself
need not extend continuously to every real boundary parameter.  Its inverted coordinate can still
extend continuously to the whole closed upper half-plane.  At a parameter where that coordinate
is nonzero, inversion recovers a continuous finite-valued extension of the original map.

This file transfers the local half-plane and sector descriptions of a polygonal domain to that
finite-valued extension.  Boundary parameters on a side map to its supporting line, parameters at
a finite vertex map to the two bounding rays, and nearby points of the open upper half-plane map
into the corresponding half-plane or sector.  The results provide the finite side and corner data
used by the Schwarz--Christoffel formula even when other boundary parameters represent vertices at
infinity.

## Main results

* `TauCeti.exists_ball_side_of_inverted_coordinate` gives the local side condition at a nonzero
  boundary value of the inverted coordinate.
* `TauCeti.exists_ball_corner_of_inverted_coordinate` gives the local finite-corner condition.

## References

* C. Carathéodory, Über die gegenseitige Beziehung der Ränder bei der konformen Abbildung,
  Math. Ann. 73 (1913).
* Ch. Pommerenke, *Boundary Behaviour of Conformal Maps*, Springer, 1992, Ch. 2.
-/

public section

open Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {g : ℂ → ℂ} {q : ℂ} {U : Set ℂ}

/-- Localize the finite part of an inverted boundary coordinate. -/
private theorem exists_ball_finite_boundary_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hgU : (fun z => q + (g z)⁻¹) '' upperHalfPlaneSet = U) {x : ℝ} (hx : g x ≠ 0)
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ r > 0,
      ContinuousOn (fun z => q + (g z)⁻¹) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn (fun z => q + (g z)⁻¹) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ ball (x : ℂ) r, 0 ≤ z.im →
        q + (g z)⁻¹ ∈ ball (q + (g x)⁻¹) rho) ∧
      ∀ z ∈ ball (x : ℂ) r, z.im = 0 → q + (g z)⁻¹ ∈ frontier U := by
  let F : ℂ → ℂ := fun z => q + (g z)⁻¹
  have hxH : ((x : ℝ) : ℂ) ∈ {z : ℂ | 0 ≤ z.im} := by simp
  have hgcx : ContinuousWithinAt g {z : ℂ | 0 ≤ z.im} (x : ℂ) := hgc _ hxH
  have hFcx : ContinuousWithinAt F {z : ℂ | 0 ≤ z.im} (x : ℂ) :=
    continuousWithinAt_const.add (hgcx.inv₀ hx)
  obtain ⟨r₁, hr₁, hFball⟩ := Metric.continuousWithinAt_iff.mp hFcx rho hrho
  have hgne : ∀ᶠ z in 𝓝[{z : ℂ | 0 ≤ z.im}] (x : ℂ), g z ≠ 0 := hgcx.eventually_ne hx
  obtain ⟨r₂, hr₂, hgball⟩ := Metric.mem_nhdsWithin_iff.mp hgne
  let r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  have hnonzero {z : ℂ} (hz : z ∈ ball (x : ℂ) r) (hzH : 0 ≤ z.im) : g z ≠ 0 :=
    hgball ⟨Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_right _ _)), hzH⟩
  have hFcont : ContinuousOn F (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) :=
    continuousOn_const.add <| (hgc.mono inter_subset_right).inv₀ fun z hz =>
      hnonzero hz.1 hz.2
  have hFinj : InjOn F (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) := by
    intro z hz w hw hzw
    apply hgi ⟨hz.2, hnonzero hz.1 hz.2⟩ ⟨hw.2, hnonzero hw.1 hw.2⟩
    apply inv_injective
    apply add_left_cancel (a := q)
    simpa only [F] using hzw
  have himage {z : ℂ} (hz : z ∈ ball (x : ℂ) r) (hzH : 0 ≤ z.im) :
      F z ∈ ball (F x) rho :=
    hFball hzH (Metric.mem_ball.mpr ((Metric.mem_ball.mp hz).trans_le (min_le_left _ _)))
  have hnot {z : ℂ} (hz : z ∈ ball (x : ℂ) r) (hz0 : z.im = 0) :
      F z ∉ F '' upperHalfPlaneSet := by
    rintro ⟨y, hy, hyz⟩
    have hyH : 0 ≤ y.im := le_of_lt hy
    have hyne : g y ≠ 0 := by
      intro hgy
      have hyq : F y = q := by simp [F, hgy]
      have hzq : F z = q := hyz.symm.trans hyq
      exact hnonzero hz hz0.ge (by simpa [F] using hzq)
    have hginv : (g y)⁻¹ = (g z)⁻¹ := by
      apply add_left_cancel (a := q)
      simpa only [F] using hyz
    have hgz : g z = g y := inv_injective hginv.symm
    have hzy : z = y := hgi ⟨hz0.ge, hnonzero hz hz0.ge⟩ ⟨hyH, hyne⟩ hgz
    have hypos : 0 < y.im := hy
    rw [← hzy, hz0] at hypos
    exact (lt_irrefl 0) hypos
  refine ⟨r, hr, hFcont, hFinj, fun z hz hzH => himage hz hzH, fun z hz hz0 => ?_⟩
  exact hgU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero
    (continuousWithinAt_const.add ((hgc z hz0.ge).inv₀ (hnonzero hz hz0.ge)))
    hz0 (hnot hz hz0)

/-- Near a nonzero boundary value of a continuous inverted coordinate, the recovered finite map
`z ↦ q + (g z)⁻¹` is continuous and injective on the closed upper half-plane.  Its real
boundary values lie on the supporting line of a local side of `U`, and its interior values lie on
the side of that line occupied by `U`.

The injectivity hypothesis is only imposed where `g` is nonzero.  Thus it applies to inverted
coordinates with several boundary zeros, one for each access of the original domain to infinity. -/
theorem exists_ball_side_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hgU : (fun z => q + (g z)⁻¹) '' upperHalfPlaneSet = U) {x : ℝ} (hx : g x ≠ 0)
    {p b : ℂ} {rho : ℝ} (hrho : 0 < rho)
    (hU : ∀ z ∈ ball (q + (g x)⁻¹) rho, (z ∈ U ↔ 0 < ((z - p) / b).im)) :
    ∃ r > 0,
      ContinuousOn (fun z => q + (g z)⁻¹) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn (fun z => q + (g z)⁻¹) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ ball (x : ℂ) r, z.im = 0 → (((q + (g z)⁻¹) - p) / b).im = 0) ∧
      ∀ z ∈ ball (x : ℂ) r, 0 < z.im → 0 < (((q + (g z)⁻¹) - p) / b).im := by
  obtain ⟨r, hr, hcont, hinj, hball, hfrontier⟩ :=
    exists_ball_finite_boundary_of_inverted_coordinate hgc hgi hgU hx hrho
  refine ⟨r, hr, hcont, hinj, fun z hz hz0 => ?_, fun z hz hz0 => ?_⟩
  · exact im_div_eq_zero_of_mem_frontier hU (hball z hz hz0.ge) (hfrontier z hz hz0)
  · exact (hU _ (hball z hz hz0.le)).mp (hgU ▸ mem_image_of_mem _ hz0)

/-- Near a nonzero boundary value of a continuous inverted coordinate, a local sector description
of `U` gives the complete finite-corner condition for the recovered map `z ↦ q + (g z)⁻¹`.
Interior points map into the sector, while every other nearby real boundary value lies on one of
its two bounding rays. -/
theorem exists_ball_corner_of_inverted_coordinate
    (hgc : ContinuousOn g {z : ℂ | 0 ≤ z.im})
    (hgi : InjOn g {z : ℂ | 0 ≤ z.im ∧ g z ≠ 0})
    (hgU : (fun z => q + (g z)⁻¹) '' upperHalfPlaneSet = U) {x : ℝ} (hx : g x ≠ 0)
    {b : ℂ} {rho alpha : ℝ} (hrho : 0 < rho) (hb : b ≠ 0)
    (hU : ∀ z ∈ ball (q + (g x)⁻¹) rho, z ≠ q + (g x)⁻¹ →
      (z ∈ U ↔ |((z - (q + (g x)⁻¹)) / b).arg| < alpha)) :
    ∃ r > 0,
      ContinuousOn (fun z => q + (g z)⁻¹) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      InjOn (fun z => q + (g z)⁻¹) (ball (x : ℂ) r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ ball (x : ℂ) r, 0 < z.im →
        |(((q + (g z)⁻¹) - (q + (g x)⁻¹)) / b).arg| < alpha) ∧
      ∀ z ∈ ball (x : ℂ) r, z.im = 0 → q + (g z)⁻¹ ≠ q + (g x)⁻¹ →
        |(((q + (g z)⁻¹) - (q + (g x)⁻¹)) / b).arg| = alpha := by
  obtain ⟨r, hr, hcont, hinj, hball, hfrontier⟩ :=
    exists_ball_finite_boundary_of_inverted_coordinate hgc hgi hgU hx hrho
  refine ⟨r, hr, hcont, hinj, fun z hz hz0 => ?_, fun z hz hz0 hzx => ?_⟩
  · have hzx : q + (g z)⁻¹ ≠ q + (g x)⁻¹ := fun h => by
      have := hinj ⟨hz, hz0.le⟩ ⟨mem_ball_self hr, by simp⟩ h
      simp [this] at hz0
    exact (hU _ (hball z hz hz0.le) hzx).mp (hgU ▸ mem_image_of_mem _ hz0)
  · exact abs_arg_div_eq_of_mem_frontier hb isOpen_ball hU (hball z hz hz0.ge) hzx
      (hfrontier z hz hz0)

end TauCeti

end
