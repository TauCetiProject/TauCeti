/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Segment
public import TauCeti.Analysis.Complex.UpperHalfPlane.IdealRegion
import Mathlib.Topology.MetricSpace.HausdorffDistance
import TauCeti.Analysis.Complex.NormSq
import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Basic
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.FromTo
import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Orientation

/-!
# Perpendicular bisectors and distance half-planes

For distinct `p q : ℍ`, `perpBisector p q` represents the oriented geodesic bisecting the segment
from `p` to `q`. Its open left half-plane consists of the points closer to `p`, its closed
left half-plane consists of the points at least as close to `p`, and its line consists of the
points equidistant from the two centres. In particular, distance dominance regions are
geodesically convex, the geometric ingredient in convexity of Dirichlet domains. The
equidistant locus has zero invariant area (`volume_setOf_dist_eq_dist`), as every geodesic
line does. A closed geodesically convex set can be separated from an exterior point by
the bisector between the point and its nearest point in the set
(`exists_subset_closure_leftHalfPlane_of_isClosed`).

The closed Euclidean half-planes `{z | a ≤ Re z}` and `{z | Re z ≤ b}` bounded by vertical lines,
and the closed exteriors `{z | ρ ≤ |z - c|²}` of discs centred on the real axis, are such
distance dominance regions, so they are geodesically convex too
(`geodesicSegment_subset_setOf_le_re`, `geodesicSegment_subset_setOf_re_le`,
`geodesicSegment_subset_setOf_le_normSq_sub`). Ford polygons are cut out by such sets.

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

/-- In the imaginary-axis coordinates `w = (geodesicBetween p q)⁻¹ • z`, the difference of the
hyperbolic cosines of the distances from `z` to `p` and `q` is explicit in `w`: it equals
`(exp (dist p q) - 1) * (exp (-(dist p q / 2)) ^ 2 * ‖w‖ ^ 2 - 1) / (2 * w.im)`, so for `p ≠ q`
its sign is that of `exp (-(dist p q / 2)) ^ 2 * ‖w‖ ^ 2 - 1`. -/
private theorem cosh_dist_sub_cosh_dist_eq_of_inv_smul (p q z : ℍ) :
    Real.cosh (dist z p) - Real.cosh (dist z q) =
      (Real.exp (dist p q) - 1) * (Real.exp (-(dist p q / 2)) ^ 2 *
        Complex.normSq (((geodesicBetween p q)⁻¹ • z : ℍ) : ℂ) - 1) /
          (2 * ((geodesicBetween p q)⁻¹ • z : ℍ).im) := by
  -- The inverse half-distance dilation scales squared norms by `exp (-d)`.
  have ha : Real.exp (-(dist p q / 2)) ^ 2 * Real.exp (dist p q) = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    have hd : -(dist p q / 2) + -(dist p q / 2) + dist p q = 0 := by ring
    rw [hd, Real.exp_zero]
  rw [← dist_smul (geodesicBetween p q)⁻¹ z p, ← dist_smul (geodesicBetween p q)⁻¹ z q,
    inv_geodesicBetween_smul_left p q, inv_geodesicBetween_smul_right p q, cosh_dist',
    cosh_dist', geodesicLine_one_apply]
  simp only [UpperHalfPlane.I_re, UpperHalfPlane.I_im, UpperHalfPlane.mk_re,
    UpperHalfPlane.mk_im, sub_zero, one_pow, mul_one]
  simp only [Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  generalize ((geodesicBetween p q)⁻¹ • z : ℍ) = w
  generalize Real.exp (-(dist p q / 2)) = a at ha ⊢
  have hw := w.im_pos.ne'
  have he0 := (Real.exp_pos (dist p q)).ne'
  field_simp [hw, he0]
  linear_combination -(w.re ^ 2 + w.im ^ 2) * (Real.exp (dist p q) - 1) * ha

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
  have he : 1 < Real.exp d := Real.one_lt_exp_iff.mpr (dist_pos.mpr hpq)
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
  have hc : Real.cosh (dist z p) - Real.cosh (dist z q) =
      (Real.exp d - 1) * (a ^ 2 * Complex.normSq (w : ℂ) - 1) / (2 * w.im) :=
    cosh_dist_sub_cosh_dist_eq_of_inv_smul p q z
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

/-- Closed half-planes `{z | a ≤ z.re}` bounded by a vertical line are geodesically convex. -/
theorem geodesicSegment_subset_setOf_le_re {a : ℝ} {z w : ℍ} (hz : a ≤ z.re) (hw : a ≤ w.re) :
    geodesicSegment z w ⊆ {u : ℍ | a ≤ u.re} := by
  have key (u : ℍ) : a ≤ u.re ↔ dist u ((a + 1) +ᵥ I) ≤ dist u ((a - 1) +ᵥ I) := by
    rw [dist_le_dist_iff_re_im, vadd_re, vadd_re, vadd_im, vadd_im, I_re, I_im]
    constructor <;> intro h <;> nlinarith
  exact fun u hu ↦ (key u).2 <|
    geodesicSegment_subset_setOf_dist_le_dist ((key z).1 hz) ((key w).1 hw) hu

/-- Closed half-planes `{z | z.re ≤ b}` bounded by a vertical line are geodesically convex. -/
theorem geodesicSegment_subset_setOf_re_le {b : ℝ} {z w : ℍ} (hz : z.re ≤ b) (hw : w.re ≤ b) :
    geodesicSegment z w ⊆ {u : ℍ | u.re ≤ b} := by
  have key (u : ℍ) : u.re ≤ b ↔ dist u ((b - 1) +ᵥ I) ≤ dist u ((b + 1) +ᵥ I) := by
    rw [dist_le_dist_iff_re_im, vadd_re, vadd_re, vadd_im, vadd_im, I_re, I_im]
    constructor <;> intro h <;> nlinarith
  exact fun u hu ↦ (key u).2 <|
    geodesicSegment_subset_setOf_dist_le_dist ((key z).1 hz) ((key w).1 hw) hu

/-- The closed exterior `{z | ρ ≤ |z - c|²}` of a disc centred on the real axis is geodesically
convex: for `ρ > 0` it is the closed half-plane bounded by the semicircle of radius `√ρ` about
`c`, and for `ρ ≤ 0` it is all of `ℍ`. -/
theorem geodesicSegment_subset_setOf_le_normSq_sub {c ρ : ℝ} {z w : ℍ}
    (hz : ρ ≤ Complex.normSq ((z : ℂ) - c)) (hw : ρ ≤ Complex.normSq ((w : ℂ) - c)) :
    geodesicSegment z w ⊆ {u : ℍ | ρ ≤ Complex.normSq ((u : ℂ) - c)} := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · exact fun u _ ↦ hρ.trans (Complex.normSq_nonneg _)
  set r := Real.sqrt ρ
  have hr : 0 < r := Real.sqrt_pos.2 hρ
  have hr2 : r ^ 2 = ρ := Real.sq_sqrt hρ.le
  -- The semicircle of radius `r` about `c` bisects `c + 2ri` and `c + ri/2`.
  set p : ℍ := mk (c + (2 * r : ℝ) * Complex.I) (by simp [hr])
  set q : ℍ := mk (c + (r / 2 : ℝ) * Complex.I) (by simp [hr])
  have key (u : ℍ) : ρ ≤ Complex.normSq ((u : ℂ) - c) ↔ dist u p ≤ dist u q := by
    rw [dist_le_dist_iff_re_im, Complex.normSq_sub_ofReal, coe_re, coe_im, ← hr2]
    simp only [p, q, mk_re, mk_im, Complex.add_re, Complex.add_im, Complex.re_ofReal_mul,
      Complex.im_ofReal_mul, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    constructor <;> intro h <;> nlinarith
  exact fun u hu ↦ (key u).2 <|
    geodesicSegment_subset_setOf_dist_le_dist ((key z).1 hz) ((key w).1 hw) hu

/-- No open half-plane bounded by the perpendicular bisector of two centres contains both
centres, whichever orientation of the bisector is chosen. For distinct centres this says that
they lie strictly on opposite sides of the bisector; at coincident centres the chosen line passes
through the common centre. -/
theorem notMem_leftHalfPlane_of_range_eq_perpBisector {p q : ℍ} {k : PSL(2, ℝ)}
    (hk : range (geodesicLine (perpBisector p q)) = range (geodesicLine k))
    (hp : p ∈ leftHalfPlane k) : q ∉ leftHalfPlane k := by
  rcases eq_or_ne p q with rfl | hpq
  · -- The arbitrary line through `p` chosen at coincident centres contains `p`.
    refine absurd ?_ (disjoint_left.mp (disjoint_leftHalfPlane_range_geodesicLine k) hp)
    rw [← hk]
    refine ⟨0, ?_⟩
    rw [geodesicLine_zero, perpBisector_def, dist_self, zero_div, mul_assoc, mul_smul]
    simp [← geodesicLine_zero]
  rcases exists_eq_mul_dilation_or_eq_mul_pslS_mul_dilation_of_range_eq hk with
    ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [leftHalfPlane_mul_dilation, mem_leftHalfPlane_perpBisector_iff hpq, dist_self]
    exact dist_nonneg.not_gt
  · rw [leftHalfPlane_mul_dilation, leftHalfPlane_mul_pslS,
      mem_rightHalfPlane_perpBisector_iff hpq, dist_self] at hp
    exact absurd hp dist_nonneg.not_gt

private theorem cosh_dist_geodesicLine_one (w : ℍ) (t : ℝ) :
    Real.cosh (dist w (geodesicLine 1 t)) =
      (w.re ^ 2 + w.im ^ 2 + Real.exp t ^ 2) / (2 * w.im * Real.exp t) := by
  rw [cosh_dist', geodesicLine_one_apply]
  simp only [UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, sub_zero]

private theorem normSq_le_one_of_dist_geodesicLine_min {w : ℍ} {d : ℝ} (hd : 0 < d)
    (h : ∀ t ∈ Icc 0 d, dist w (geodesicLine 1 0) ≤ dist w (geodesicLine 1 t)) :
    w.re ^ 2 + w.im ^ 2 ≤ 1 := by
  by_contra! hn
  -- At any height strictly between 1 and the squared norm, the distance decreases.
  let a := min (Real.exp d) ((w.re ^ 2 + w.im ^ 2 + 1) / 2)
  have ha : 1 < a := lt_min (Real.one_lt_exp_iff.2 hd) (by linarith)
  have ha' : 0 < a := zero_lt_one.trans ha
  have haNorm : a < w.re ^ 2 + w.im ^ 2 := (min_le_right _ _).trans_lt (by linarith)
  have ht : Real.log a ∈ Icc 0 d := ⟨Real.log_nonneg ha.le,
    (Real.log_le_iff_le_exp ha').2 (min_le_left _ _)⟩
  have hle : Real.cosh (dist w (geodesicLine 1 0)) ≤
      Real.cosh (dist w (geodesicLine 1 (Real.log a))) := by
    simpa only [Real.cosh_le_cosh, abs_of_nonneg dist_nonneg] using h (Real.log a) ht
  rw [cosh_dist_geodesicLine_one, cosh_dist_geodesicLine_one, Real.exp_zero, Real.exp_log ha',
    one_pow, mul_one, div_le_div_iff₀ (by positivity) (by positivity)] at hle
  have hneg : (2 * w.im) * ((a - 1) * (a - (w.re ^ 2 + w.im ^ 2))) < 0 :=
    mul_neg_of_pos_of_neg (by positivity)
      (mul_neg_of_pos_of_neg (sub_pos.2 ha) (sub_neg.2 haNorm))
  nlinarith only [hle, hneg]

private theorem dist_geodesicLine_one_le_dist_of_normSq_le_one {w : ℍ} {d : ℝ}
    (hd : 0 ≤ d) (h : w.re ^ 2 + w.im ^ 2 ≤ 1) :
    dist (geodesicLine 1 0) (geodesicLine 1 d) ≤ dist w (geodesicLine 1 d) := by
  have him : w.im ≤ 1 := by
    nlinarith only [w.im_pos, h, sq_nonneg w.re]
  have he := Real.one_le_exp_iff.2 hd
  rw [← abs_of_nonneg (dist_nonneg (x := geodesicLine 1 0) (y := geodesicLine 1 d)),
    ← abs_of_nonneg (dist_nonneg (x := w) (y := geodesicLine 1 d)), ← Real.cosh_le_cosh]
  rw [cosh_dist_geodesicLine_one, cosh_dist_geodesicLine_one,
    geodesicLine_one_apply (t := 0)]
  simp only [UpperHalfPlane.mk_re, UpperHalfPlane.mk_im, Real.exp_zero,
    zero_pow (by decide : 2 ≠ 0), one_pow, zero_add, mul_one]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  -- The distance comparison at height 1 is nonnegative, and only increases with height.
  have hnonneg : 0 ≤ (2 * Real.exp d) *
      (w.re ^ 2 + (w.im - 1) ^ 2 + (1 - w.im) * (Real.exp d ^ 2 - 1)) := by
    exact mul_nonneg (by positivity) (add_nonneg (by positivity)
      (mul_nonneg (sub_nonneg.2 him) (by nlinarith only [he, sq_nonneg (Real.exp d - 1)])))
  nlinarith only [hnonneg]

/-- If the initial point of a geodesic segment minimizes distance to a point along the
segment, then the other endpoint is at least as close to the initial point as to the given point. -/
theorem dist_le_dist_of_forall_mem_geodesicSegment {x p q : ℍ}
    (h : ∀ z ∈ geodesicSegment p q, dist x p ≤ dist x z) : dist q p ≤ dist q x := by
  by_cases hpq : p = q
  · simp [← hpq]
  let g := geodesicBetween p q
  let w : ℍ := g⁻¹ • x
  have hg (t : ℝ) : g⁻¹ • geodesicLine g t = geodesicLine 1 t := by
    rw [smul_geodesicLine, inv_mul_cancel]
  have h0 : g⁻¹ • p = geodesicLine 1 0 := by
    rw [← hg, geodesicLine_geodesicBetween_zero]
  have hd : g⁻¹ • q = geodesicLine 1 (dist p q) := by
    rw [← hg, geodesicLine_geodesicBetween_dist]
  have hmin (t : ℝ) (ht : t ∈ Icc 0 (dist p q)) :
      dist w (geodesicLine 1 0) ≤ dist w (geodesicLine 1 t) := by
    rw [← h0, ← hg]
    simpa only [w, dist_smul] using h _ ((mem_geodesicSegment_iff _ _ _).2 ⟨t, ht, rfl⟩)
  rw [dist_comm q p, dist_comm q x, ← dist_smul g⁻¹ p q, ← dist_smul g⁻¹ x q, h0, hd]
  exact dist_geodesicLine_one_le_dist_of_normSq_le_one dist_nonneg
    (normSq_le_one_of_dist_geodesicLine_min (dist_pos.2 hpq) hmin)

/-- A point outside a closed geodesically convex set is separated from it by a closed
geodesic half-plane. -/
theorem exists_subset_closure_leftHalfPlane_of_isClosed {C : Set ℍ} (hC : IsClosed C)
    (hconv : ∀ ⦃p q⦄, p ∈ C → q ∈ C → geodesicSegment p q ⊆ C) {x : ℍ} (hx : x ∉ C) :
    ∃ g : PSL(2, ℝ), C ⊆ closure (leftHalfPlane g) ∧ x ∉ closure (leftHalfPlane g) := by
  have exclude {p : ℍ} (hpx : p ≠ x) : x ∉ closure (leftHalfPlane (perpBisector p x)) := by
    rw [mem_closure_leftHalfPlane_perpBisector_iff hpx, dist_self, not_le]
    exact dist_pos.2 hpx.symm
  rcases C.eq_empty_or_nonempty with rfl | hne
  · obtain ⟨p, hp⟩ := exists_ne x
    exact ⟨perpBisector p x, empty_subset _, exclude hp⟩
  obtain ⟨p, hp, hpdist⟩ := hC.exists_infDist_eq_dist hne x
  have hpx : p ≠ x := fun e ↦ hx (e ▸ hp)
  refine ⟨perpBisector p x, fun q hq ↦ ?_, exclude hpx⟩
  rw [mem_closure_leftHalfPlane_perpBisector_iff hpx]
  exact dist_le_dist_of_forall_mem_geodesicSegment fun z hz ↦
    hpdist ▸ Metric.infDist_le_dist_of_mem (hconv hp hq hz)

end TauCeti.UpperHalfPlane
