/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Segment
public import TauCeti.Analysis.Complex.UpperHalfPlane.IdealRegion

/-!
# Perpendicular bisectors and distance half-planes

For distinct `p q : ℍ`, `perpBisector p q` represents the oriented geodesic bisecting the segment
from `p` to `q`. Its open left half-plane consists of the points closer to `p`, its closed
left half-plane consists of the points at least as close to `p`, and its line consists of the
points equidistant from the two centres. In particular, distance dominance regions are
geodesically convex, the geometric ingredient in convexity of Dirichlet domains. The
equidistant locus has zero invariant area (`volume_setOf_dist_eq_dist`), as every geodesic
line does.

The construction moves the segment onto the imaginary axis, dilates to its midpoint, and
rotates by `π / 4` in `SL(2, ℝ)`, which rotates the tangent by `π / 2`.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.
-/

public section

noncomputable section

open UpperHalfPlane Set
open Matrix.SpecialLinearGroup (rotation dilation)
open scoped MatrixGroups Pointwise

namespace TauCeti.UpperHalfPlane

/-- The oriented perpendicular bisector of `p` and `q`, represented as a projective isometry.
For distinct centres its left half-plane contains `p`. At coincident centres this is an
arbitrary line through that point, not the equidistant locus. -/
def perpBisector (p q : ℍ) : PSL(2, ℝ) :=
  geodesicBetween p q * ↑(dilation (dist p q / 2)) * ↑(rotation (Real.pi / 4))

/-- The perpendicular bisector is obtained by moving to the midpoint of the oriented segment
and rotating its tangent through a right angle. -/
theorem perpBisector_def (p q : ℍ) :
    perpBisector p q =
      geodesicBetween p q * ↑(dilation (dist p q / 2)) * ↑(rotation (Real.pi / 4)) :=
  (rfl)

/-- The real part of `(perpBisector p q)⁻¹ • z` is a positive multiple of
`Real.cosh (dist z p) - Real.cosh (dist z q)`. -/
private theorem exists_pos_re_inv_perpBisector_smul_eq {p q : ℍ} (hpq : p ≠ q) (z : ℍ) :
    ∃ κ : ℝ, 0 < κ ∧ ((perpBisector p q)⁻¹ • z : ℍ).re =
      κ * (Real.cosh (dist z p) - Real.cosh (dist z q)) := by
  let g := geodesicBetween p q
  let w : ℍ := g⁻¹ • z
  let d := dist p q
  -- In these imaginary-axis coordinates, both the signed side of the bisector and the
  -- difference of the two hyperbolic cosines are positive multiples of `|w|² - exp d`.
  let a := Real.exp (-(d / 2))
  let v : ℍ := (↑(dilation (d / 2)) : PSL(2, ℝ))⁻¹ • w
  let N := Complex.normSq ((Real.sin (Real.pi / 4) : ℂ) * v + Real.cos (Real.pi / 4))
  have h0 : g⁻¹ • p = UpperHalfPlane.I := by
    rw [inv_smul_eq_iff, ← geodesicLine_zero, geodesicLine_geodesicBetween_zero]
  have h1 : g⁻¹ • q = geodesicLine 1 d := by
    rw [inv_smul_eq_iff, smul_geodesicLine, mul_one, geodesicLine_geodesicBetween_dist]
  have he : 1 < Real.exp d := Real.one_lt_exp_iff.mpr (dist_pos.mpr hpq)
  -- The inverse half-distance dilation scales squared norms by `exp (-d)`.
  have ha : a ^ 2 * Real.exp d = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    have hd : -(d / 2) + -(d / 2) + d = 0 := by ring
    rw [hd, Real.exp_zero]
  have hN : 0 < N := normSq_sin_mul_add_cos_pos _ v
  have hn : Complex.normSq (v : ℂ) = a ^ 2 * Complex.normSq (w : ℂ) := by
    dsimp only [v]
    rw [← QuotientGroup.mk_inv, Matrix.SpecialLinearGroup.dilation_inv,
      UpperHalfPlane.pslMk_smul, coe_dilation_smul, map_mul, Complex.normSq_ofReal]
    ring
  -- The quarter-angle rotation tests whether the rescaled point is inside the unit circle.
  have hr : ((perpBisector p q)⁻¹ • z : ℍ).re =
      (a ^ 2 * Complex.normSq (w : ℂ) - 1) / (2 * N) := by
    have hr' : ((perpBisector p q)⁻¹ • z : ℍ).re =
        (((↑(rotation (Real.pi / 4)) : PSL(2, ℝ))⁻¹ • v : ℍ)).re := by
      simp only [perpBisector, mul_inv_rev, mul_smul, v, w, g, d]
    have ht : Real.sin (Real.pi / 4) * Real.cos (Real.pi / 4) = 1 / 2 := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by positivity)]
    have ht' : Real.cos (Real.pi / 4) ^ 2 - Real.sin (Real.pi / 4) ^ 2 = 0 := by
      rw [Real.sin_pi_div_four, Real.cos_pi_div_four, sub_self]
    rw [hr', re_rotation_inv_smul, ht, ht', zero_mul, add_zero, hn]
    ring
  -- Compare distances in the imaginary-axis coordinates using Mathlib's cosine formula.
  have hc : Real.cosh (dist z p) - Real.cosh (dist z q) =
      (Real.exp d - 1) * (a ^ 2 * Complex.normSq (w : ℂ) - 1) / (2 * w.im) := by
    rw [← dist_smul g⁻¹ z p, ← dist_smul g⁻¹ z q, h0, h1, cosh_dist', cosh_dist',
      geodesicLine_one_apply]
    simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, UpperHalfPlane.mk_re,
      UpperHalfPlane.mk_im, sub_zero, one_pow, mul_one]
    simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    have hw := w.im_pos.ne'
    have he0 := (Real.exp_pos d).ne'
    dsimp only [w] at hw ⊢
    field_simp [hw, he0]
    linear_combination -(w.re ^ 2 + w.im ^ 2) * (Real.exp d - 1) * ha
  refine ⟨w.im / ((Real.exp d - 1) * N),
    div_pos w.im_pos (mul_pos (sub_pos.mpr he) hN), ?_⟩
  rw [hr, hc]
  have hw := w.im_pos.ne'
  have he0 := (sub_pos.mpr he).ne'
  have hN0 := hN.ne'
  field_simp

-- The generic half-plane membership lemmas already determine the `simp` normal form.
/-- The points closer to `p` than to `q` form the open left half-plane of their perpendicular
bisector. -/
theorem mem_leftHalfPlane_perpBisector_iff {p q : ℍ} (hpq : p ≠ q) (z : ℍ) :
    z ∈ leftHalfPlane (perpBisector p q) ↔ dist z p < dist z q := by
  obtain ⟨κ, hκ, h⟩ := exists_pos_re_inv_perpBisector_smul_eq hpq z
  rw [mem_leftHalfPlane_iff, h, mul_neg_iff]
  simp only [hκ, hκ.not_gt, false_and, or_false, true_and, sub_neg,
    Real.cosh_lt_cosh, abs_of_nonneg dist_nonneg]

/-- The points closer to `q` than to `p` form the open right half-plane of their perpendicular
bisector. -/
theorem mem_rightHalfPlane_perpBisector_iff {p q : ℍ} (hpq : p ≠ q) (z : ℍ) :
    z ∈ rightHalfPlane (perpBisector p q) ↔ dist z q < dist z p := by
  obtain ⟨κ, hκ, h⟩ := exists_pos_re_inv_perpBisector_smul_eq hpq z
  rw [mem_rightHalfPlane_iff, h, mul_pos_iff_of_pos_left hκ, sub_pos]
  simp only [Real.cosh_lt_cosh, abs_of_nonneg dist_nonneg]

/-- The perpendicular bisector is exactly the hyperbolic equidistant locus. -/
theorem mem_range_geodesicLine_perpBisector_iff {p q : ℍ} (hpq : p ≠ q) (z : ℍ) :
    z ∈ range (geodesicLine (perpBisector p q)) ↔ dist z p = dist z q := by
  obtain ⟨κ, hκ, h⟩ := exists_pos_re_inv_perpBisector_smul_eq hpq z
  rw [mem_range_geodesicLine_iff, h, mul_eq_zero, or_iff_right hκ.ne', sub_eq_zero]
  simp only [le_antisymm_iff, Real.cosh_le_cosh, abs_of_nonneg dist_nonneg]

/-- **Hyperbolic perpendicular bisectors are null.** The points of `ℍ` equidistant from two
distinct points have zero invariant area. -/
theorem volume_setOf_dist_eq_dist {p q : ℍ} (hpq : p ≠ q) :
    MeasureTheory.volume {z : ℍ | dist z p = dist z q} = 0 := by
  have h : {z : ℍ | dist z p = dist z q} = range (geodesicLine (perpBisector p q)) :=
    Set.ext fun z ↦ (mem_range_geodesicLine_perpBisector_iff hpq z).symm
  rw [h, volume_range_geodesicLine]

/-- The points at least as close to `p` as to `q` form a closed geodesic half-plane. -/
theorem mem_closure_leftHalfPlane_perpBisector_iff {p q : ℍ} (hpq : p ≠ q) (z : ℍ) :
    z ∈ closure (leftHalfPlane (perpBisector p q)) ↔ dist z p ≤ dist z q := by
  rw [closure_leftHalfPlane, mem_union, mem_leftHalfPlane_perpBisector_iff hpq,
    mem_range_geodesicLine_perpBisector_iff hpq, le_iff_lt_or_eq]

/-- The points at least as close to `q` as to `p` form the opposite closed half-plane. -/
theorem mem_closure_rightHalfPlane_perpBisector_iff {p q : ℍ} (hpq : p ≠ q) (z : ℍ) :
    z ∈ closure (rightHalfPlane (perpBisector p q)) ↔ dist z q ≤ dist z p := by
  rw [closure_rightHalfPlane, mem_union, mem_rightHalfPlane_perpBisector_iff hpq,
    mem_range_geodesicLine_perpBisector_iff hpq, le_iff_lt_or_eq, eq_comm]

/-- A hyperbolic distance dominance region contains the geodesic segment joining any two
of its points. No distinctness assumption on the centres is needed. -/
theorem geodesicSegment_subset_setOf_dist_le_dist {p q z w : ℍ}
    (hz : dist z p ≤ dist z q) (hw : dist w p ≤ dist w q) :
    geodesicSegment z w ⊆ {u : ℍ | dist u p ≤ dist u q} := by
  rcases eq_or_ne p q with rfl | hpq
  · simp
  · intro u hu
    exact (mem_closure_leftHalfPlane_perpBisector_iff hpq u).mp <|
      geodesicSegment_subset_closure_leftHalfPlane
        ((mem_closure_leftHalfPlane_perpBisector_iff hpq z).mpr hz)
        ((mem_closure_leftHalfPlane_perpBisector_iff hpq w).mpr hw) hu

end TauCeti.UpperHalfPlane
