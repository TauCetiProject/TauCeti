/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Convex
import TauCeti.Topology.Frontier

/-!
# Affine bijections of horizontal strips

Positive real scalings and complex translations map horizontal strips bijectively
onto the strips whose endpoints undergo the corresponding real affine map. These
maps rescale logarithmic strip coordinates to arbitrary boundary heights.

An open set of the plane whose frontier is, to the right of some `R`, exactly the two horizontal
lines bounding a strip, and which misses a point of the strip to the right of `R`, agrees to the
right of `R` with the complement of the closed strip.
-/

public section

namespace TauCeti

open Complex Set

/-- A positive real scaling followed by a complex translation maps a horizontal strip
bijectively onto the strip with the transformed imaginary endpoints. -/
theorem bijOn_ofReal_mul_add_horizontalStrip {s : ℝ} (hs : 0 < s) (c : ℂ) (l h : ℝ) :
    BijOn (fun w : ℂ => (s : ℂ) * w + c)
      {w : ℂ | w.im ∈ Ioo l h} {w : ℂ | w.im ∈ Ioo (s * l + c.im) (s * h + c.im)} :=
  ((Equiv.mulLeft₀ (s : ℂ) (ofReal_ne_zero.mpr hs.ne')).trans (Equiv.addRight c)).bijOn
    fun w => by simp [hs]

/-- If the frontier of an open set `U ⊆ ℂ` is, to the right of `R`, exactly the two horizontal
lines at heights `lo` and `hi`, and a point `z` of the band between them to the right of `R` is not
in `U`, then every point of `U` to the right of `R` lies strictly below or strictly above the
band. -/
private theorem im_lt_or_lt_im_of_mem_of_frontier_eq {U : Set ℂ} (hUo : IsOpen U) {R hi lo : ℝ}
    (hline : ∀ w : ℂ, R < w.re → (w ∈ frontier U ↔ w.im = hi ∨ w.im = lo)) {z : ℂ}
    (hzR : R < z.re) (hzlo : lo < z.im) (hzhi : z.im < hi) (hz : z ∉ U) {w : ℂ} (hwR : R < w.re)
    (hwU : w ∈ U) : w.im < lo ∨ hi < w.im := by
  have hne : w ∉ frontier U := by
    rw [hUo.frontier_eq]
    exact fun h => h.2 hwU
  rw [hline w hwR, not_or] at hne
  by_contra! hw
  have hS := (convex_halfSpace_re_gt R).inter ((convex_halfSpace_im_gt lo).inter
    (convex_halfSpace_im_lt hi)) |>.isPreconnected.subset_of_disjoint_frontier
    (Set.disjoint_left.mpr fun v hv hvfr => by
      have := (hline v hv.1).mp hvfr
      rcases this with h | h
      · exact hv.2.2.ne h
      · exact hv.2.1.ne' h)
    ⟨w, ⟨hwR, lt_of_le_of_ne hw.1 (Ne.symm hne.2), lt_of_le_of_ne hw.2 hne.1⟩, hwU⟩
  exact hz (hS ⟨hzR, hzlo, hzhi⟩)

/-- If the frontier of an open set `U ⊆ ℂ` is, to the right of `R`, exactly the two horizontal
lines at heights `lo` and `hi`, and a point `z` of the band between them to the right of `R` is
not in `U`, then to the right of `R` the set `U` is exactly the set of points strictly below or
strictly above the band. -/
theorem mem_iff_im_lt_or_lt_im_of_frontier_eq {U : Set ℂ} (hUo : IsOpen U) {R hi lo : ℝ}
    (hline : ∀ w : ℂ, R < w.re → (w ∈ frontier U ↔ w.im = hi ∨ w.im = lo))
    {z : ℂ} (hzR : R < z.re) (hzlo : lo < z.im) (hzhi : z.im < hi) (hz : z ∉ U) {w : ℂ}
    (hwR : R < w.re) : w ∈ U ↔ w.im < lo ∨ hi < w.im := by
  have hgap : lo < hi := hzlo.trans hzhi
  have hout {w : ℂ} (hwR : R < w.re) (hwU : w ∈ U) : w.im < lo ∨ hi < w.im :=
    im_lt_or_lt_im_of_mem_of_frontier_eq hUo hline hzR hzlo hzhi hz hwR hwU
  -- Each line lies in the closure of `U`, so points of `U` come close to it.
  have hnear (h : ℝ) (hh : h = hi ∨ h = lo) :
      ∃ u ∈ U, R < u.re ∧ |u.im - h| < (hi - lo) / 2 := by
    have hw₀ : (⟨R + 1, h⟩ : ℂ) ∈ closure U :=
      frontier_subset_closure ((hline _ (lt_add_one R)).mpr hh)
    obtain ⟨u, huU, hu⟩ := Metric.mem_closure_iff.mp hw₀ (min 1 ((hi - lo) / 2))
      (lt_min one_pos (by linarith))
    rw [dist_eq_norm] at hu
    have hre := (abs_lt.mp ((abs_re_le_norm _).trans_lt (hu.trans_le (min_le_left _ _)))).2
    have him := (abs_im_le_norm _).trans_lt (hu.trans_le (min_le_right _ _))
    simp only [sub_re, sub_im] at hre him
    rw [abs_sub_comm] at him
    exact ⟨u, huU, by linarith, him⟩
  have habove : {w : ℂ | R < w.re ∧ hi < w.im} ⊆ U := by
    obtain ⟨u, huU, huR, hu⟩ := hnear hi (Or.inl rfl)
    refine ((convex_halfSpace_re_gt R).inter
      (convex_halfSpace_im_gt hi)).isPreconnected.subset_of_disjoint_frontier
      (Set.disjoint_left.mpr fun v hv hvfr => ?_)
      ⟨u, ⟨huR, (hout huR huU).resolve_left fun h => ?_⟩, huU⟩
    · rcases (hline v hv.1).mp hvfr with h | h
      · exact hv.2.ne' h
      · exact (hgap.trans hv.2).ne' h
    · linarith [(abs_lt.mp hu).1]
  have hbelow : {w : ℂ | R < w.re ∧ w.im < lo} ⊆ U := by
    obtain ⟨u, huU, huR, hu⟩ := hnear lo (Or.inr rfl)
    refine ((convex_halfSpace_re_gt R).inter
      (convex_halfSpace_im_lt lo)).isPreconnected.subset_of_disjoint_frontier
      (Set.disjoint_left.mpr fun v hv hvfr => ?_)
      ⟨u, ⟨huR, (hout huR huU).resolve_right fun h => ?_⟩, huU⟩
    · rcases (hline v hv.1).mp hvfr with h | h
      · exact (hv.2.trans hgap).ne h
      · exact hv.2.ne h
    · linarith [(abs_lt.mp hu).2]
  exact ⟨hout hwR, fun hw => hw.elim (fun h => hbelow ⟨hwR, h⟩) (fun h => habove ⟨hwR, h⟩)⟩

end TauCeti
