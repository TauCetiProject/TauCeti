/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Conformal.SchwarzChristoffel.Formula

import TauCeti.Analysis.Complex.Conformal.LocalDegree
import TauCeti.Analysis.Complex.UpperHalfPlane.Topology
import Mathlib.Analysis.Complex.Angle

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

This file derives from these global conditions the local side, corner and infinity conditions of
`TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary`, and so proves
that such an `f` is an affine image of the normalized Schwarz--Christoffel primitive for the
prevertices `a i` and the turning exponents `e i`.  The only geometric input is local: a
boundary value of `f` lies on the frontier of `U`, and near a side or a vertex that frontier lies
on the bounding line or on the two bounding rays.

## Main result

* `TauCeti.eqOn_const_mul_schwarzChristoffelPrimitive_add_of_injOn_of_image_eq` -- a conformal
  map of the upper half-plane onto a polygonal domain, continuous and injective up to the real
  axis and tending to a side at infinity, is an affine image of the Schwarz--Christoffel
  primitive.

## References

* L. Ahlfors, *Complex Analysis*, Ch. 6, Section 2.
* T. Driscoll and L. Trefethen, *Schwarz--Christoffel Mapping*, Ch. 2.
-/

public section

open Bornology Complex Filter Function Metric Set Topology UpperHalfPlane

namespace TauCeti

variable {U : Set ℂ}

/-! ### The frontier near a side and near a vertex -/

/-- Near a boundary point where `U` coincides with an open half-plane, the frontier of `U` lies on
the bounding line. -/
private theorem im_div_eq_zero_of_mem_frontier {w q b z : ℂ} {ρ : ℝ}
    (hU : ∀ y ∈ ball w ρ, (y ∈ U ↔ 0 < ((y - q) / b).im)) (hz : z ∈ ball w ρ)
    (hzU : z ∈ frontier U) : ((z - q) / b).im = 0 := by
  have hUO : U ∩ ball w ρ = {y : ℂ | 0 < ((y - q) / b).im} ∩ ball w ρ :=
    Set.ext fun y => and_congr_left (hU y)
  have h : z ∈ frontier {y : ℂ | 0 < ((y - q) / b).im} ∩ ball w ρ := by
    rw [← frontier_inter_open_inter isOpen_ball, ← hUO, frontier_inter_open_inter isOpen_ball]
    exact ⟨hzU, hz⟩
  exact (frontier_lt_subset_eq continuous_const (by fun_prop) h.1).symm

/-- Near a vertex where `U` coincides with the open sector `{|arg ((z - v) / b)| < α}`, the
frontier of `U` away from the vertex lies on the two bounding rays `|arg ((z - v) / b)| = α`. -/
private theorem abs_arg_div_eq_of_mem_frontier {v b z : ℂ} {ρ α : ℝ} (hb : b ≠ 0)
    (hU : ∀ y ∈ ball v ρ, y ≠ v → (y ∈ U ↔ |((y - v) / b).arg| < α)) (hz : z ∈ ball v ρ)
    (hzv : z ≠ v) (hzU : z ∈ frontier U) : |((z - v) / b).arg| = α := by
  set O := ball v ρ \ {v}
  have hO : IsOpen O := isOpen_ball.sdiff isClosed_singleton
  -- `|arg|` is the unoriented angle with `1`, which is continuous away from `0`
  have hφ : ContinuousOn (fun y : ℂ => |((y - v) / b).arg|) O := fun y hy => by
    have hy0 : (y - v) / b ≠ 0 := div_ne_zero (sub_ne_zero.mpr hy.2) hb
    have hangle : ContinuousAt (fun y : ℂ => InnerProductGeometry.angle ((y - v) / b) 1) y :=
      (InnerProductGeometry.continuousAt_angle (x := ((y - v) / b, (1 : ℂ))) hy0
        one_ne_zero).comp (f := fun y : ℂ => ((y - v) / b, (1 : ℂ))) (by fun_prop)
    refine (hangle.congr ?_).continuousWithinAt
    filter_upwards [isOpen_ne.mem_nhds hy.2] with y hy
    exact angle_one_right (div_ne_zero (sub_ne_zero.mpr hy) hb)
  -- on the punctured ball `U` is the strict sublevel set of `|arg|`
  have hfr : (⟨z, hz, hzv⟩ : O) ∈ frontier {y : O | |((y - v : ℂ) / b).arg| < α} := by
    rw [← show ((↑) : O → ℂ) ⁻¹' U = {y : O | |((y - v : ℂ) / b).arg| < α} from
      Set.ext fun y => hU y y.2.1 y.2.2,
      ← hO.isOpenMap_subtype_val.preimage_frontier_eq_frontier_preimage continuous_subtype_val]
    exact hzU
  exact frontier_lt_subset_eq hφ.domRestrict continuous_const hfr

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
      (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero hfc hfi hz0)
  · exact (hU _ (hball hz0.le hz)).mp (hfU ▸ mem_image_of_mem f hz0)

/-- **Corner condition.**  Near a real point `x` whose image is a vertex of `U`, the nearby upper
half-plane is carried into the open sector at that vertex and the other boundary values of `f`
onto its two bounding rays. -/
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
  · exact abs_arg_div_eq_of_mem_frontier hb hU (hball hz0.symm.le hz) hzx
      (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero hfc hfi hz0)

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
  have hmem : ∀ w ∈ upperHalfPlaneSet, -w⁻¹ ∈ upperHalfPlaneSet := fun w (hw : 0 < w.im) => by
    simpa [upperHalfPlaneSet, neg_div, one_div, inv_neg] using
      (⟨w, hw⟩ : ℍ).im_inv_neg_coe_pos
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
        (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero hfc hfi (by simp [hw0]))
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

/-! ### The Schwarz--Christoffel formula -/

/-- **The Schwarz--Christoffel formula for a conformal map onto a polygonal domain.**  Let `U`
coincide near each boundary point that is not a vertex with an open half-plane, and near the
vertex `v i` with the open sector of opening `(e i + 1) * π` at `v i`.  Let `f` be holomorphic on
the upper half-plane, map it onto `U`, and extend to a continuous injection of the closed upper
half-plane with `f (a i) = v i`; suppose also that `f z` tends at infinity to a point `p` which
is not a value of `f` on the closed upper half-plane.  Then throughout the upper half-plane

`f z = (f'(z₀) / integrand(z₀)) * F z + f z₀`,

where `F` is the normalized Schwarz--Christoffel primitive for the prevertices `a` and the turning
exponents `e`. -/
theorem eqOn_const_mul_schwarzChristoffelPrimitive_add_of_injOn_of_image_eq
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
      schwarzChristoffelPrimitive a e z₀ z + f z₀) upperHalfPlaneSet := by
  have hH0 : upperHalfPlaneSet ⊆ {z : ℂ | 0 ≤ z.im} := ofPred_subset_ofPred.mpr fun _ => le_of_lt
  have hvf : ∀ i, v i ∈ f '' {z : ℂ | 0 ≤ z.im} := fun i => ⟨(a i : ℂ), by simp, hfv i⟩
  refine eqOn_const_mul_schwarzChristoffelPrimitive_add_of_polygonal_boundary a e ha he z₀ hf
    (fun z hz => deriv_ne_zero_of_injOn hf isOpen_upperHalfPlaneSet (hfi.mono hH0) hz)
    (fun x hx => ?_) (fun i => ?_) ?_
  · -- a real point that is not a prevertex is carried to a side
    have hxv : ∀ i, f x ≠ v i := fun i h =>
      hx i (by exact_mod_cast hfi (by simp) (by simp) ((hfv i).trans h.symm))
    obtain ⟨ρ, hρ, q, b, hb, hU⟩ :=
      hside _ (hfU ▸ mem_frontier_image_upperHalfPlaneSet_of_im_eq_zero hfc hfi (ofReal_im x)) hxv
    obtain ⟨r, hr, hreal, hupper⟩ := exists_ball_im_div_of_image_eq hfc hfi hfU (ofReal_im x) hρ hU
    exact ⟨r, hr, q, b, hb, hfc.mono inter_subset_right, hfi.mono inter_subset_right, hreal,
      hupper⟩
  · -- the prevertex `a i` is carried to the vertex `v i`
    obtain ⟨ρ, hρ, b, hb, hU⟩ := hcorner i
    rw [← hfv i] at hU
    obtain ⟨r, hr, hupper, hreal⟩ :=
      exists_ball_abs_arg_div_of_image_eq hfc hfi hfU (ofReal_im (a i)) hρ hb hU
    exact ⟨r, hr, b, hb, hfc.mono inter_subset_right, hfi.mono inter_subset_right, hupper, hreal⟩
  · -- infinity is carried to the point `p` on a side
    have hpU : p ∈ frontier U := by
      refine ⟨?_, fun h => hpf ?_⟩
      · exact mem_closure_of_tendsto (hp.mono_left (inf_le_inf_left _ (principal_mono.mpr hH0)))
          (eventually_inf_principal.mpr (Eventually.of_forall fun z hz =>
            hfU ▸ mem_image_of_mem f hz))
      · obtain ⟨y, hy, hyp⟩ := hfU.symm ▸ interior_subset h
        exact ⟨y, hH0 hy, hyp⟩
    obtain ⟨ρ, hρ, q, b, hb, hU⟩ := hside p hpU fun i h => hpf (h ▸ hvf i)
    obtain ⟨r, hr, g, hg⟩ := exists_eqOn_neg_inv_of_tendsto hfc hfi hfU hp hpf hpU hρ hb hU
    exact ⟨r, hr, g, q, b, hb, hg⟩

end TauCeti

end
