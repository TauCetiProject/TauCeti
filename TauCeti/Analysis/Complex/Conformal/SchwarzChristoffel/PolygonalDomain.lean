/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Formula

import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.Conformal.LocalFrontier
import TauCeti.Analysis.Complex.Conformal.Reflection.Infinity
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology

/-!
# Conformal maps of the upper half-plane onto polygonal domains

A **polygonal domain** is described here by its local geometry at its boundary points: near a
boundary point `w` that is not a vertex the domain `U` coincides with an open half-plane
`{z | 0 < ((z - q) / b).im}`, and near the vertex `v i` it coincides with the open sector of
opening `(e i + 1) * π` at `v i`.  Both convex and reentrant vertices are allowed.

Let `f` be a holomorphic bijection of the upper half-plane onto such a domain `U` that extends to
a continuous injection of the closed upper half-plane, with prevertices `f (a i) = v i`, and that
tends at infinity to a boundary point `p` of `U` which is not a vertex and is not a boundary value
of `f`.  These are the properties that Carathéodory's boundary correspondence supplies for a
Riemann map of a polygon, once it is transported to the upper half-plane with infinity sent to a
boundary point that is not a vertex; that transport is not carried out here.

An **unbounded polygonal domain** has, besides finitely many vertices, a vertex at infinity:
far from some point `c` it coincides with the open sector `{|arg ((z - c) / b)| < β * π / 2}` of
opening `β * π`, where `0 < β < 2`, so that its two unbounded sides lie on lines through `c`.  For
such a domain the map `f` is instead required to tend to infinity at infinity, so that the point
at infinity of the half-plane is the prevertex of the vertex at infinity.  This excludes the
degenerate openings `β = 0` and `β = 2`, whose two unbounded sides are parallel, as for a strip.
That a Riemann map of such a domain has these properties is not established here.

This file derives from these global conditions the local side and corner conditions of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary`, together with the
limit of `z * f''(z) / f'(z)` at infinity, which is `-2` in the bounded case and `β - 1` in the
unbounded one, and so proves that such an `f` is an affine image of the normalized
Schwarz--Christoffel primitive for the prevertices `a i` and the turning exponents `e i`.  The
only geometric input is local: a boundary value of `f` lies on the frontier of `U`, and near a
side or a vertex, or far out along an unbounded side, that frontier lies on the bounding line or
on the two bounding rays.

## Main results

* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain` -- a conformal
  map of the upper half-plane onto a polygonal domain, continuous and injective up to the real
  axis and tending to a side at infinity, is an affine image of the Schwarz--Christoffel
  primitive.
* `TauCeti.exponent_sum_eq_neg_two_of_polygonal_domain` -- the turning exponents of such a polygonal
  domain sum to `-2`: its interior angles sum to `(n - 2) * π`.
* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_unbounded_polygonal_domain` -- a
  conformal map of the upper half-plane onto an unbounded polygonal domain, continuous and
  injective up to the real axis and tending to infinity at infinity, is an affine image of the
  Schwarz--Christoffel primitive.
* `TauCeti.exponent_sum_eq_sub_one_of_unbounded_polygonal_domain` -- the turning exponents of the
  finite vertices of such a domain sum to `β - 1`.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {U : Set ℂ}

/-! ### Boundary values of a conformal map onto `U` -/

variable {f : ℂ → ℂ}

/-- **Side condition.**  Near a real point `x` whose image lies on a side of `U`, the boundary
values of `f` run along the line of that side and the nearby upper half-plane is carried to the
side of that line on which `U` lies. -/
private theorem exists_ball_im_div_of_image_eq (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U) {x q b : ℂ} {ρ : ℝ}
    (hx : x.im = 0) (hρ : 0 < ρ) (hU : ∀ z ∈ ball (f x) ρ, (z ∈ U ↔ 0 < ((z - q) / b).im)) :
    ∃ r > 0, (∀ z ∈ ball x r, z.im = 0 → ((f z - q) / b).im = 0) ∧
      ∀ z ∈ ball x r, 0 < z.im → 0 < ((f z - q) / b).im := by
  obtain ⟨r, hr, hball⟩ := Metric.continuousWithinAt_iff.mp (hfc x hx.symm.le) ρ hρ
  refine ⟨r, hr, fun z hz hz0 => ?_, fun z hz hz0 => ?_⟩
  · exact im_div_eq_zero_of_mem_frontier hU (hball hz0.symm.le hz)
      (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero
        (hfc _ hz0.symm.le) hz0 (not_mem_image_upperHalfPlaneSet_of_im_eq_zero hfi hz0))
  · exact (hU _ (hball hz0.le hz)).mp (hfU ▸ mem_image_of_mem f hz0)

/-- **Corner condition.**  Near a real point `x` whose image is a vertex of `U`, the nearby upper
half-plane is carried into the open sector at that vertex and the other boundary values of `f`
lie on its two bounding rays. -/
private theorem exists_ball_abs_arg_div_of_image_eq (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U) {x b : ℂ} {ρ α : ℝ}
    (hx : x.im = 0) (hρ : 0 < ρ) (hb : b ≠ 0)
    (hU : ∀ z ∈ ball (f x) ρ, z ≠ f x → (z ∈ U ↔ |((z - f x) / b).arg| < α)) :
    ∃ r > 0, (∀ z ∈ ball x r, 0 < z.im → |((f z - f x) / b).arg| < α) ∧
      ∀ z ∈ ball x r, z.im = 0 → f z ≠ f x → |((f z - f x) / b).arg| = α := by
  obtain ⟨r, hr, hball⟩ := Metric.continuousWithinAt_iff.mp (hfc x hx.symm.le) ρ hρ
  refine ⟨r, hr, fun z hz hz0 => ?_, fun z hz hz0 hzx => ?_⟩
  · have hzx : f z ≠ f x := fun h => by
      simp [hfi hz0.le hx.symm.le h, hx] at hz0
    exact (hU _ (hball hz0.le hz) hzx).mp (hfU ▸ mem_image_of_mem f hz0)
  · exact abs_arg_div_eq_of_mem_frontier hb isOpen_ball hU (hball hz0.symm.le hz) hzx
      (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero
        (hfc _ hz0.symm.le) hz0 (not_mem_image_upperHalfPlaneSet_of_im_eq_zero hfi hz0))

/-- **Condition at infinity.**  If `f` tends at infinity to a point `p` on a side of `U` which is
not a value of `f`, then in the coordinate `w ↦ -w⁻¹` at infinity, and after normalizing that side
to the real axis, `f` extends continuously and injectively across `0`, with real boundary values
and the upper half-plane mapped into the upper half-plane. -/
private theorem exists_eqOn_neg_inv_of_tendsto (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U) {p q b : ℂ} {ρ : ℝ}
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 p))
    (hpf : p ∉ f '' {z : ℂ | 0 ≤ z.im}) (hpU : p ∈ frontier U) (hρ : 0 < ρ) (hb : b ≠ 0)
    (hU : ∀ z ∈ ball p ρ, (z ∈ U ↔ 0 < ((z - q) / b).im)) :
    ∃ r > 0, ∃ g : ℂ → ℂ,
      EqOn g (fun w => (f (-w⁻¹) - q) / b) (ball 0 r ∩ upperHalfPlaneSet) ∧
      ContinuousOn g (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) ∧
      (∀ z ∈ ball (0 : ℂ) r, z.im = 0 → (g z).im = 0) ∧
      MapsTo g (ball 0 r ∩ upperHalfPlaneSet) upperHalfPlaneSet ∧
      InjOn g (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) := by
  -- `w ↦ -w⁻¹` carries the closed half-plane near `0` to the closed half-plane near infinity
  have hT : Tendsto (fun w => f (-w⁻¹)) (𝓝[{w : ℂ | 0 ≤ w.im} \ {0}] 0) (𝓝 p) := by
    refine hp.comp (tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩)
    · exact (tendsto_neg_cobounded.comp tendsto_inv₀_nhdsNE_zero).mono_left
        (nhdsWithin_mono _ fun w hw => hw.2)
    · exact eventually_nhdsWithin_of_forall fun w hw => im_neg_inv_nonneg.mpr hw.1
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ w ∈ ball (0 : ℂ) r, 0 ≤ w.im → w ≠ 0 →
      f (-w⁻¹) ∈ ball p ρ := by
    obtain ⟨r, hr, h⟩ := Metric.mem_nhdsWithin_iff.mp (hT (ball_mem_nhds p hρ))
    exact ⟨r, hr, fun w hw hw0 hw1 => h ⟨hw, hw0, hw1⟩⟩
  have hne : ∀ w ∈ upperHalfPlaneSet, w ≠ 0 := fun w (hw : 0 < w.im) h => by
    simp [h] at hw
  have hmem : ∀ w ∈ upperHalfPlaneSet, -w⁻¹ ∈ upperHalfPlaneSet :=
    fun _ hw => im_neg_inv_pos.mpr hw
  -- the value `(p - q) / b` at `0` is not taken elsewhere
  have hnotp : ∀ w : ℂ, 0 ≤ w.im → (p - q) / b ≠ (f (-w⁻¹) - q) / b := fun w hw h => by
    rw [div_left_inj' hb, sub_left_inj] at h
    exact hpf ⟨-w⁻¹, im_neg_inv_nonneg.mpr hw, h.symm⟩
  refine ⟨r, hr, update (fun w => (f (-w⁻¹) - q) / b) 0 ((p - q) / b),
    fun w hw => update_of_ne (hne w hw.2) _ _, ?_, fun w hw hw0 => ?_, fun w hw => ?_,
    fun w₁ hw₁ w₂ hw₂ h => ?_⟩
  · refine continuousOn_update_iff.mpr ⟨fun w hw => ?_, fun _ => ?_⟩
    · have hinv : ContinuousWithinAt (fun w : ℂ => -w⁻¹) ((ball 0 r ∩ {z | 0 ≤ z.im}) \ {0}) w :=
        (continuousAt_inv₀ hw.2).neg.continuousWithinAt
      exact (((hfc _ (im_neg_inv_nonneg.mpr hw.1.2)).comp (f := fun w : ℂ => -w⁻¹) hinv
        fun y (hy : y ∈ (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) \ {0}) =>
          im_neg_inv_nonneg.mpr hy.1.2).sub_const q).div_const b
    · exact ((hT.mono_left (nhdsWithin_mono _
        (sdiff_subset_sdiff_left inter_subset_right))).sub_const q).div_const b
  · by_cases h0 : w = 0
    · subst h0
      rw [update_self]
      exact im_div_eq_zero_of_mem_frontier hU (mem_ball_self hρ) hpU
    · rw [update_of_ne h0]
      exact im_div_eq_zero_of_mem_frontier hU (hball w hw hw0.symm.le h0)
        (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero
          (hfc _ (by simp [hw0])) (by simp [hw0])
          (not_mem_image_upperHalfPlaneSet_of_im_eq_zero hfi (by simp [hw0])))
  · rw [update_of_ne (hne w hw.2)]
    exact (hU _ (hball w hw.1 hw.2.le (hne w hw.2))).mp
      (hfU ▸ mem_image_of_mem f (hmem w hw.2))
  · by_cases h₁ : w₁ = 0 <;> by_cases h₂ : w₂ = 0
    · rw [h₁, h₂]
    · rw [h₁, update_self, update_of_ne h₂] at h
      exact (hnotp w₂ hw₂.2 h).elim
    · rw [h₂, update_self, update_of_ne h₁] at h
      exact (hnotp w₁ hw₁.2 h.symm).elim
    · rw [update_of_ne h₁, update_of_ne h₂, div_left_inj' hb, sub_left_inj] at h
      simpa using hfi (im_neg_inv_nonneg.mpr hw₁.2) (im_neg_inv_nonneg.mpr hw₂.2) h

/-- **Condition at infinity, from the global data.**  If `f` tends at infinity to a point `p`
which is not a value of `f` on the closed upper half-plane, and hence not a vertex, then `p` lies on
a side of `U`, and `z * f''(z) / f'(z) → -2` as `z` tends to infinity in the upper half-plane. -/
private theorem tendsto_mul_logDeriv_deriv_of_tendsto_of_side {ι : Type*} {a : ι → ℝ}
    {v : ι → ℂ} {p : ℂ} (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im}) (hfi : InjOn f {z : ℂ | 0 ≤ z.im})
    (hfU : f '' upperHalfPlaneSet = U) (hfv : ∀ i, f (a i) = v i)
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 p))
    (hpf : p ∉ f '' {z : ℂ | 0 ≤ z.im})
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im)) :
    Tendsto (fun z => z * logDeriv (deriv f) z) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 (-2)) := by
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hpU : p ∈ frontier U := by
    refine ⟨?_, fun h => hpf ?_⟩
    · exact mem_closure_of_tendsto (hp.mono_left (inf_le_inf_left _ (principal_mono.mpr hH0)))
        (eventually_inf_principal.mpr (Eventually.of_forall fun z hz =>
          hfU ▸ mem_image_of_mem f hz))
    · obtain ⟨y, hy, hyp⟩ := hfU.symm ▸ interior_subset h
      exact ⟨y, hH0 hy, hyp⟩
  obtain ⟨ρ, hρ, q, b, hb, hU⟩ :=
    hside p hpU fun i h => hpf ⟨(a i : ℂ), by simp, (hfv i).trans h.symm⟩
  obtain ⟨r, hr, g, hgf, hgcont, hgreal, hgupper, hginj⟩ :=
    exists_eqOn_neg_inv_of_tendsto hfc hfi hfU hp hpf hpU hρ hb hU
  exact tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_neg_inv hr hb hgf hgcont
    (differentiableOn_of_eqOn_neg_inv hf hgf) hgreal hgupper hginj

/-- **Condition at a vertex at infinity.**  If `f` tends to infinity at infinity, and far from `c`
the domain `U` coincides with the open sector `{|arg ((z - c) / b)| < β * π / 2}` of opening
`β * π`, where `0 < β < 2`, then `z * f''(z) / f'(z) → β - 1` as `z` tends to infinity in the
upper half-plane. -/
private theorem tendsto_mul_logDeriv_deriv_of_tendsto_cobounded {β ρ : ℝ} {c b : ℂ}
    (hβ : β ∈ Ioo (0 : ℝ) 2) (hb : b ≠ 0) (hf : DifferentiableOn ℂ f upperHalfPlaneSet)
    (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im}) (hfi : InjOn f {z : ℂ | 0 ≤ z.im})
    (hfU : f '' upperHalfPlaneSet = U)
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cobounded ℂ))
    (hU : ∀ z : ℂ, ρ < ‖z - c‖ → (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    Tendsto (fun z => z * logDeriv (deriv f) z) (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet)
      (𝓝 ((β : ℂ) - 1)) := by
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn hf isOpen_upperHalfPlaneSet (hfi.mono hH0) hz
  -- `w ↦ -w⁻¹` carries the closed half-plane near `0` to the closed half-plane near infinity
  have hT : Tendsto (fun w => f (-w⁻¹)) (𝓝[{w : ℂ | 0 ≤ w.im} \ {0}] 0) (cobounded ℂ) := by
    refine hp.comp (tendsto_inf.mpr ⟨?_, tendsto_principal.mpr ?_⟩)
    · exact (tendsto_neg_cobounded.comp tendsto_inv₀_nhdsNE_zero).mono_left
        (nhdsWithin_mono _ fun w hw => hw.2)
    · exact eventually_nhdsWithin_of_forall fun w hw => im_neg_inv_nonneg.mpr hw.1
  -- near `0`, the inverse coordinate stays in the region where `U` is the sector
  obtain ⟨r, hr, hfar⟩ : ∃ r > 0, ∀ w ∈ ball (0 : ℂ) r, 0 ≤ w.im → w ≠ 0 →
      max ρ 0 < ‖f (-w⁻¹) - c‖ := by
    obtain ⟨r, hr, h⟩ := Metric.mem_nhdsWithin_iff.mp
      (hT ((Metric.hasBasis_cobounded_compl_closedBall c).mem_of_mem (i := max ρ 0) trivial))
    exact ⟨r, hr, fun w hw hw0 hw1 => by simpa [dist_eq_norm] using h ⟨hw, hw0, hw1⟩⟩
  have hne : ∀ w ∈ ball (0 : ℂ) r, 0 ≤ w.im → w ≠ 0 → f (-w⁻¹) - c ≠ 0 :=
    fun w hw hw0 hw1 h => by
      have hlt := (le_max_right ρ 0).trans_lt (hfar w hw hw0 hw1)
      rw [h, norm_zero] at hlt
      exact lt_irrefl _ hlt
  have hH : ∀ w ∈ upperHalfPlaneSet, w ≠ 0 := fun w (hw : 0 < w.im) h => by simp [h] at hw
  -- invert the target about `c`, filling in the value `0` at the origin
  set g : ℂ → ℂ := update (fun w => b / (f (-w⁻¹) - c)) 0 0
  have hg0 : g 0 = 0 := update_self _ _ _
  have hgv : ∀ w, w ≠ 0 → g w = b / (f (-w⁻¹) - c) := fun w hw => update_of_ne hw _ _
  have harg : ∀ w, w ≠ 0 → |(g w).arg| = |((f (-w⁻¹) - c) / b).arg| := fun w hw => by
    rw [hgv w hw, ← inv_div, abs_arg_inv]
  refine tendsto_mul_logDeriv_deriv_upperHalfPlaneSet_of_eqOn_div_neg_inv (g := g) hr hb hβ hf hfn
    (fun w hw => hgv w (hH w hw.2)) hg0 ?_ ?_ (fun w hw hwim => ?_)
    (fun w hw hwim hgw => ?_)
  · refine continuousOn_update_iff.mpr ⟨fun w hw => ?_, fun _ => ?_⟩
    · have hinv : ContinuousWithinAt (fun w : ℂ => -w⁻¹) ((ball 0 r ∩ {z | 0 ≤ z.im}) \ {0}) w :=
        (continuousAt_inv₀ hw.2).neg.continuousWithinAt
      exact continuousWithinAt_const.div (((hfc _ (im_neg_inv_nonneg.mpr hw.1.2)).comp
        (f := fun w : ℂ => -w⁻¹) hinv fun y (hy : y ∈ (ball 0 r ∩ {z : ℂ | 0 ≤ z.im}) \ {0}) =>
          im_neg_inv_nonneg.mpr hy.1.2).sub_const c) (hne w hw.1.1 hw.1.2 hw.2)
    · have hlim := (tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded c).comp
        (hT.mono_left (nhdsWithin_mono _
          (sdiff_subset_sdiff_left (inter_subset_right (s := ball (0 : ℂ) r))))))).const_mul b
      simpa only [mul_zero, Function.comp_def, div_eq_mul_inv] using hlim
  · intro w₁ hw₁ w₂ hw₂ h
    by_cases h₁ : w₁ = 0 <;> by_cases h₂ : w₂ = 0
    · rw [h₁, h₂]
    · rw [h₁, hg0, hgv w₂ h₂] at h
      exact absurd h.symm (div_ne_zero hb (hne w₂ hw₂.1 hw₂.2 h₂))
    · rw [h₂, hg0, hgv w₁ h₁] at h
      exact absurd h (div_ne_zero hb (hne w₁ hw₁.1 hw₁.2 h₁))
    · rw [hgv w₁ h₁, hgv w₂ h₂] at h
      have h' := congrArg (·⁻¹) h
      simp only [inv_div, div_left_inj' hb, sub_left_inj] at h'
      simpa using hfi (im_neg_inv_nonneg.mpr hw₁.2) (im_neg_inv_nonneg.mpr hw₂.2) h'
  · -- the far part of the upper half-plane goes into the sector
    have hw0 : w ≠ 0 := hH w hwim
    rw [harg w hw0]
    exact (hU _ ((le_max_left ρ 0).trans_lt (hfar w hw hwim.le hw0))).mp
      (hfU ▸ mem_image_of_mem f (im_neg_inv_pos.mpr hwim))
  · -- and the far parts of the real axis go to the two bounding rays
    have hw0 : w ≠ 0 := fun h => hgw (h ▸ hg0)
    have him : (-w⁻¹).im = 0 := by simp [hwim]
    rw [harg w hw0]
    exact abs_arg_div_eq_of_mem_frontier (V := {y : ℂ | ρ < ‖y - c‖}) hb
      (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm)
      (fun y hy _ => hU y hy) ((le_max_left ρ 0).trans_lt (hfar w hw hwim.ge hw0))
      (sub_ne_zero.mp (hne w hw hwim.ge hw0))
      (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero
        (hfc _ him.ge) him (not_mem_image_upperHalfPlaneSet_of_im_eq_zero hfi him))

/-! ### The Schwarz--Christoffel formula -/

/-- The Schwarz--Christoffel formula for a conformal map onto a polygonal domain, given the
limit `L` of `z * f''(z) / f'(z)` at infinity; the bounded and unbounded cases differ only in how
that limit is obtained. -/
private theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain_of_tendsto
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (ha : Function.Injective a)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane) {v : ι → ℂ} {L : ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U)
    (hfv : ∀ i, f (a i) = v i)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : Tendsto (fun z => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 L)) :
    EqOn f (fun z => deriv f z₀ / schwarzChristoffelIntegrand a e z₀ *
      schwarzChristoffelPrimitive a e z₀ z + f z₀) upperHalfPlaneSet := by
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  refine eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary a e ha he z₀ hf
    (fun z hz => deriv_ne_zero_of_injOn hf isOpen_upperHalfPlaneSet (hfi.mono hH0) hz)
    (fun x hx => ?_) (fun i => ?_) hinfty
  · -- a real point that is not a prevertex is carried to a side
    have hxv : ∀ i, f x ≠ v i := fun i h =>
      hx i (by exact_mod_cast hfi (by simp) (by simp) ((hfv i).trans h.symm))
    obtain ⟨ρ, hρ, q, b, hb, hU⟩ :=
      hside _ (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero
        (hfc _ (by simp)) (ofReal_im x)
        (not_mem_image_upperHalfPlaneSet_of_im_eq_zero hfi (ofReal_im x))) hxv
    obtain ⟨r, hr, hreal, hupper⟩ := exists_ball_im_div_of_image_eq hfc hfi hfU (ofReal_im x) hρ hU
    exact ⟨r, hr, q, b, hb, hfc.mono inter_subset_right, hfi.mono inter_subset_right, hreal,
      hupper⟩
  · -- the prevertex `a i` is carried to the vertex `v i`
    obtain ⟨ρ, hρ, b, hb, hU⟩ := hcorner i
    rw [← hfv i] at hU
    obtain ⟨r, hr, hupper, hreal⟩ :=
      exists_ball_abs_arg_div_of_image_eq hfc hfi hfU (ofReal_im (a i)) hρ hb hU
    exact ⟨r, hr, b, hb, hfc.mono inter_subset_right, hfi.mono inter_subset_right, hupper, hreal⟩

/-- The turning exponents of a polygonal domain sum to the limit `L` of `z * f''(z) / f'(z)` at
infinity, for a conformal map `f` onto it. -/
private theorem exponent_sum_eq_of_polygonal_domain_of_tendsto
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (ha : Function.Injective a)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) {v : ι → ℂ} {L : ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U)
    (hfv : ∀ i, f (a i) = v i)
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : Tendsto (fun z => z * logDeriv (deriv f) z)
      (cobounded ℂ ⊓ 𝓟 upperHalfPlaneSet) (𝓝 L)) :
    ∑ i, ((e i : ℝ) : ℂ) = L := by
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hfn : ∀ z ∈ upperHalfPlaneSet, deriv f z ≠ 0 := fun z hz =>
    deriv_ne_zero_of_injOn hf isOpen_upperHalfPlaneSet (hfi.mono hH0) hz
  -- `f` is an affine image of the primitive, so its pre-Schwarzian is the partial-fraction sum
  have hform := eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain_of_tendsto a e ha
    he UpperHalfPlane.I hf hfc hfi hfU hfv hside hcorner hinfty
  have hpre := (exists_eqOn_const_mul_schwarzChristoffelPrimitive_add_iff a e UpperHalfPlane.I
    hf hfn).mp ⟨_, div_ne_zero (hfn _ UpperHalfPlane.I.im_pos)
      (schwarzChristoffelIntegrand_ne_zero a e UpperHalfPlane.I.im_pos), _, hform⟩
  exact exponent_sum_eq_of_logDeriv_deriv_eqOn (fun i => (a i : ℂ)) (fun i => (e i : ℂ)) hpre
    hinfty

/-- **The Schwarz--Christoffel formula for a conformal map onto a polygonal domain.**  Let `U`
coincide near each boundary point that is not a vertex with an open half-plane, and near the
vertex `v i` with the open sector of opening `(e i + 1) * π` at `v i`.  Let `f` be holomorphic on
the upper half-plane, map it onto `U`, and extend to a continuous injection of the closed upper
half-plane with `f (a i) = v i`; suppose also that `f z` tends at infinity to a point `p` which
is not a value of `f` on the closed upper half-plane.  Then throughout the upper half-plane

`f z = (f'(z₀) / integrand(z₀)) * F z + f z₀`,

where `F` is the normalized Schwarz--Christoffel primitive for the prevertices `a` and the turning
exponents `e`. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (ha : Function.Injective a)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane) {v : ι → ℂ} {p : ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U)
    (hfv : ∀ i, f (a i) = v i)
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 p))
    (hpf : p ∉ f '' {z : ℂ | 0 ≤ z.im})
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2)) :
    EqOn f (fun z => deriv f z₀ / schwarzChristoffelIntegrand a e z₀ *
      schwarzChristoffelPrimitive a e z₀ z + f z₀) upperHalfPlaneSet :=
  eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain_of_tendsto a e ha he z₀ hf
    hfc hfi hfU hfv hside hcorner
    (tendsto_mul_logDeriv_deriv_of_tendsto_of_side hf hfc hfi hfU hfv hp hpf hside)

/-- **The angle sum of a polygonal domain.**  Under the hypotheses of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain`, the turning exponents
sum to `-2`.  Equivalently, the interior angles `(e i + 1) * π` of the polygon sum to
`(n - 2) * π`, where `n` is the number of vertices. -/
theorem exponent_sum_eq_neg_two_of_polygonal_domain
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (ha : Function.Injective a)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) {v : ι → ℂ} {p : ℂ}
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U)
    (hfv : ∀ i, f (a i) = v i)
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (𝓝 p))
    (hpf : p ∉ f '' {z : ℂ | 0 ≤ z.im})
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2)) :
    ∑ i, e i = -2 := by
  exact_mod_cast exponent_sum_eq_of_polygonal_domain_of_tendsto a e ha he hf hfc hfi hfU hfv hside
    hcorner (tendsto_mul_logDeriv_deriv_of_tendsto_of_side hf hfc hfi hfU hfv hp hpf hside)

/-- **The Schwarz--Christoffel formula for a conformal map onto an unbounded polygonal domain.**
Let `U` coincide near each boundary point that is not a vertex with an open half-plane, near the
vertex `v i` with the open sector of opening `(e i + 1) * π` at `v i`, and far from a point `c`
with the open sector `{|arg ((z - c) / b)| < β * π / 2}` of opening `β * π`, where `0 < β < 2`:
so `U` has, besides the finite vertices, a vertex at infinity between two unbounded sides on lines
through `c`.  Let `f` be holomorphic on the upper half-plane, map it onto `U`, and extend to a
continuous injection of the closed upper half-plane with `f (a i) = v i`; suppose also that `f z`
tends to infinity at infinity.  Then throughout the upper half-plane

`f z = (f'(z₀) / integrand(z₀)) * F z + f z₀`,

where `F` is the normalized Schwarz--Christoffel primitive for the prevertices `a` and the turning
exponents `e`. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_unbounded_polygonal_domain
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (ha : Function.Injective a)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) (z₀ : UpperHalfPlane) {v : ι → ℂ} {β : ℝ}
    (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U)
    (hfv : ∀ i, f (a i) = v i)
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cobounded ℂ))
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    EqOn f (fun z => deriv f z₀ / schwarzChristoffelIntegrand a e z₀ *
      schwarzChristoffelPrimitive a e z₀ z + f z₀) upperHalfPlaneSet := by
  obtain ⟨ρ, c, b, hb, hU⟩ := hinfty
  exact eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_domain_of_tendsto a e ha he z₀
    hf hfc hfi hfU hfv hside hcorner
    (tendsto_mul_logDeriv_deriv_of_tendsto_cobounded hβ hb hf hfc hfi hfU hp hU)

/-- **The angle sum of an unbounded polygonal domain.**  Under the hypotheses of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_unbounded_polygonal_domain`, the
turning exponents of the finite vertices sum to `β - 1`.  Equivalently, the finite vertices of the
polygon, of interior angles `(e i + 1) * π`, together with the vertex at infinity of opening
`β * π`, have interior angles summing to `(n - 2) * π` when the vertex at infinity is assigned the
angle `-β * π`, where `n` is the number of vertices including the one at infinity. -/
theorem exponent_sum_eq_sub_one_of_unbounded_polygonal_domain
    {ι : Type*} [Fintype ι] (a e : ι → ℝ) (ha : Function.Injective a)
    (he : ∀ i, e i ∈ Ioo (-1 : ℝ) 1) {v : ι → ℂ} {β : ℝ} (hβ : β ∈ Ioo (0 : ℝ) 2)
    (hf : DifferentiableOn ℂ f upperHalfPlaneSet) (hfc : ContinuousOn f {z : ℂ | 0 ≤ z.im})
    (hfi : InjOn f {z : ℂ | 0 ≤ z.im}) (hfU : f '' upperHalfPlaneSet = U)
    (hfv : ∀ i, f (a i) = v i)
    (hp : Tendsto f (cobounded ℂ ⊓ 𝓟 {z : ℂ | 0 ≤ z.im}) (cobounded ℂ))
    (hside : ∀ w ∈ frontier U, (∀ i, w ≠ v i) → ∃ ρ > 0, ∃ q b : ℂ, b ≠ 0 ∧
      ∀ z ∈ ball w ρ, (z ∈ U ↔ 0 < ((z - q) / b).im))
    (hcorner : ∀ i, ∃ ρ > 0, ∃ b : ℂ, b ≠ 0 ∧ ∀ z ∈ ball (v i) ρ, z ≠ v i →
      (z ∈ U ↔ |((z - v i) / b).arg| < (e i + 1) * Real.pi / 2))
    (hinfty : ∃ ρ : ℝ, ∃ c b : ℂ, b ≠ 0 ∧ ∀ z : ℂ, ρ < ‖z - c‖ →
      (z ∈ U ↔ |((z - c) / b).arg| < β * Real.pi / 2)) :
    ∑ i, e i = β - 1 := by
  obtain ⟨ρ, c, b, hb, hU⟩ := hinfty
  exact_mod_cast exponent_sum_eq_of_polygonal_domain_of_tendsto a e ha he hf hfc hfi hfU hfv hside
    hcorner (tendsto_mul_logDeriv_deriv_of_tendsto_cobounded hβ hb hf hfc hfi hfU hp hU)

end TauCeti

end
