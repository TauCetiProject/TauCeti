/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment

/-!
# Separating planar segments by a supporting line

Multiplication by a complex number followed by imaginary part is a real-linear
functional. Suppose this functional, applied to displacement from the first
segment's initial endpoint, vanishes on that segment and has the same strict
sign at both endpoints of another. Then the segments are disjoint. This is a
convenient signed half-plane test for polygonal boundaries with reentrant corners.
-/

public section

open Set

namespace TauCeti

/-- If a real-linear height is zero along one segment and positive at both
endpoints of a second segment, the segments are disjoint. -/
theorem disjoint_segment_of_im_mul_sub_pos (c u v w x : ℂ)
    (hline : (c * (v - u)).im = 0)
    (hw : 0 < (c * (w - u)).im) (hx : 0 < (c * (x - u)).im) :
    Disjoint (segment ℝ u v) (segment ℝ w x) := by
  rw [Set.disjoint_left]
  intro z hz₁ hz₂
  have hzero : (c * (z - u)).im = 0 := by
    rw [segment_eq_image'] at hz₁
    obtain ⟨t, _, rfl⟩ := hz₁
    simp only [add_sub_cancel_left, mul_smul_comm, Complex.smul_im,
      hline, smul_zero]
  rw [segment_eq_image'] at hz₂
  obtain ⟨t, ht, rfl⟩ := hz₂
  have hcomb : (c * (w + t • (x - w) - u)).im =
      (1 - t) * (c * (w - u)).im + t * (c * (x - u)).im := by
    have heq : w + t • (x - w) - u =
        (1 - t) • (w - u) + t • (x - u) := by
      rw [Complex.real_smul, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [heq, mul_add, mul_smul_comm, mul_smul_comm, Complex.add_im,
      Complex.smul_im, Complex.smul_im]
    simp only [smul_eq_mul]
  have hpos : 0 < (1 - t) * (c * (w - u)).im + t * (c * (x - u)).im := by
    rcases eq_or_lt_of_le ht.1 with htzero | htpos
    · subst t
      simpa only [sub_zero, one_mul, zero_mul, add_zero] using hw
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg (sub_nonneg.mpr ht.2) hw.le) (mul_pos htpos hx)
  exact hpos.ne' (hcomb ▸ hzero)

/-- The corresponding test when the second segment lies strictly on the
negative side of the supporting line. -/
theorem disjoint_segment_of_im_mul_sub_neg (c u v w x : ℂ)
    (hline : (c * (v - u)).im = 0)
    (hw : (c * (w - u)).im < 0) (hx : (c * (x - u)).im < 0) :
    Disjoint (segment ℝ u v) (segment ℝ w x) := by
  apply disjoint_segment_of_im_mul_sub_pos (-c) u v w x
  · simp only [neg_mul, Complex.neg_im, hline, neg_zero]
  · simpa only [neg_mul, Complex.neg_im] using neg_pos.mpr hw
  · simpa only [neg_mul, Complex.neg_im] using neg_pos.mpr hx

/-- A segment with one endpoint at or above a horizontal line and the other
strictly above it can meet the closed lower half-plane only at the first endpoint. -/
theorem eq_left_of_mem_segment_of_im_le_of_lt {u v z : ℂ} {h : ℝ}
    (hu : h ≤ u.im) (hv : h < v.im)
    (hz : z ∈ segment ℝ u v) (hzh : z.im ≤ h) : z = u := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hz
  simp only [Complex.add_im, Complex.smul_im, smul_eq_mul] at hzh
  have hbase : s * h + t * h = h := by rw [← add_mul, hst, one_mul]
  have ht0 : t = 0 := le_antisymm (not_lt.mp fun htpos ↦ by
    linarith [mul_le_mul_of_nonneg_left hu hs, mul_lt_mul_of_pos_left hv htpos]) ht
  have hs1 : s = 1 := by linarith
  simp [ht0, hs1]

end TauCeti
