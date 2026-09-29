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

/-- A segment on a supporting line can meet a segment with one endpoint on the line and
the other off the line only at the endpoint on the line. -/
theorem eq_left_of_mem_segment_of_im_mul_sub_ne (c u v w x z : ℂ)
    (hline : (c * (v - u)).im = 0)
    (hw : (c * (w - u)).im = 0) (hx : (c * (x - u)).im ≠ 0)
    (hz₁ : z ∈ segment ℝ u v) (hz₂ : z ∈ segment ℝ w x) : z = w := by
  have hzero : (c * (z - u)).im = 0 := by
    rw [segment_eq_image'] at hz₁
    obtain ⟨t, _, rfl⟩ := hz₁
    simp only [add_sub_cancel_left, mul_smul_comm, Complex.smul_im,
      hline, smul_zero]
  rw [segment_eq_image'] at hz₂
  obtain ⟨t, _, rfl⟩ := hz₂
  have hcomb : (c * (w + t • (x - w) - u)).im = t * (c * (x - u)).im := by
    have heq : w + t • (x - w) - u = (1 - t) • (w - u) + t • (x - u) := by
      rw [Complex.real_smul, Complex.real_smul, Complex.real_smul]
      push_cast
      ring
    rw [heq, mul_add, mul_smul_comm, mul_smul_comm, Complex.add_im,
      Complex.smul_im, Complex.smul_im, hw]
    simp
  have htzero : t = 0 := by
    have h : t * (c * (x - u)).im = 0 := hcomb ▸ hzero
    exact (mul_eq_zero.mp h).resolve_right hx
  simp [htzero]

/-- If the interior vertices of a finite polyline lie strictly on one side of a
supporting line and its endpoints lie on the line, an edge meets a segment on
the line only at a polyline endpoint. -/
theorem eq_endpoint_of_mem_segment_of_polyline_edge_of_im_mul_sub_pos {n : ℕ}
    (c u v : ℂ) (V : Fin (n + 2) → ℂ) (hn : 0 < n)
    (hline : (c * (v - u)).im = 0)
    (hfirst : (c * (V 0 - u)).im = 0)
    (hlast : (c * (V (Fin.last (n + 1)) - u)).im = 0)
    (hheight : ∀ k : Fin (n + 2), k ≠ 0 → k ≠ Fin.last (n + 1) →
      0 < (c * (V k - u)).im)
    (i : Fin (n + 1)) (z : ℂ)
    (hzline : z ∈ segment ℝ u v)
    (hzedge : z ∈ segment ℝ (V i.castSucc) (V i.succ)) :
    z = V 0 ∨ z = V (Fin.last (n + 1)) := by
  by_cases hi0 : i = 0
  · have hsucc : i.succ ≠ Fin.last (n + 1) := by
      rw [hi0, Ne, Fin.ext_iff]
      simp only [Fin.val_succ, Fin.val_zero, Fin.val_last]
      omega
    have hz := eq_left_of_mem_segment_of_im_mul_sub_ne c u v
      (V i.castSucc) (V i.succ) z hline (by simpa [hi0] using hfirst)
      (hheight i.succ (Fin.succ_ne_zero i) hsucc).ne' hzline hzedge
    exact Or.inl (by simpa [hi0] using hz)
  · have hstart : i.castSucc ≠ (0 : Fin (n + 2)) := by
      intro h
      apply hi0
      apply Fin.ext
      simpa only [Fin.val_castSucc, Fin.val_zero] using (congrArg Fin.val h)
    have hhstart := hheight i.castSucc hstart (Fin.castSucc_lt_last i).ne
    by_cases hilast : i.succ = Fin.last (n + 1)
    · have hzedge' : z ∈ segment ℝ (V i.succ) (V i.castSucc) := by
        rwa [segment_symm]
      have hz := eq_left_of_mem_segment_of_im_mul_sub_ne c u v
        (V i.succ) (V i.castSucc) z hline (by simpa [hilast] using hlast)
        hhstart.ne' hzline hzedge'
      exact Or.inr (by simpa [hilast] using hz)
    · have hhend := hheight i.succ (Fin.succ_ne_zero i) hilast
      exact ((Set.disjoint_left.mp
        (disjoint_segment_of_im_mul_sub_pos c u v
          (V i.castSucc) (V i.succ) hline hhstart hhend)) hzline hzedge).elim

end TauCeti
