/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Semicontinuity.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Point picking on preimages of balls

A large value on the preimage of the half-radius ball yields a blow-up scale inside the full
ball. Compactness is required only for preimages of closed balls of radii strictly less than
the full radius.

## References

* T. H. Colding and W. P. Minicozzi II, *The space of embedded minimal surfaces of fixed genus
  in a 3-manifold II; Multi-valued graphs in disks*, Ann. of Math. 160 (2004), Lemma 5.1.
-/

public section

open Metric Set

namespace TauCeti

variable {X Y : Type*} [PseudoMetricSpace Y]
  {f : X → Y} {g : X → ℝ} {o : Y} {R C : ℝ}

private theorem exists_pointPicking_of_strict_margin
    (hB : ∀ r < R, BddAbove (g '' (f ⁻¹' closedBall o r))) {b : X}
    (hb : 0 < g b) (hbr : dist (f b) o + 2 * (C / √(g b)) < R) :
    ∃ y, 0 < g y ∧ dist (f y) o + 2 * (C / √(g y)) ≤ R ∧
      ∀ z, f z ∈ ball (f y) (C / √(g y)) → g z ≤ 4 * g y := by
  by_cases hC : 0 ≤ C
  swap
  · refine ⟨b, hb, hbr.le, ?_⟩
    simp [ball_eq_empty.2 (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) (Real.sqrt_nonneg _))]
  obtain ⟨r, hbr', hr⟩ := exists_between hbr
  let S := f ⁻¹' closedBall o r
  let w (x : X) := (r - dist (f x) o) * √(g x)
  have hsb := Real.sqrt_pos.2 hb
  have hbS : b ∈ S := mem_closedBall.2 (by linarith [div_nonneg hC hsb.le])
  have hbweight : 2 * C < w b := (div_lt_iff₀ hsb).1 (by
    rw [mul_div_assoc]
    linarith)
  obtain ⟨G, hG⟩ := hB r hr
  have hbounded : BddAbove (w '' S) := by
    refine ⟨r * √G, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hd : dist (f z) o ≤ r := hz
    calc
      w z ≤ (r - dist (f z) o) * √G := mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (hG (mem_image_of_mem g hz))) (sub_nonneg.mpr hd)
      _ ≤ r * √G := mul_le_mul_of_nonneg_right (sub_le_self _ dist_nonneg) (Real.sqrt_nonneg _)
  have hsup := hbweight.trans_le (le_csSup hbounded (mem_image_of_mem w hbS))
  have hmid : (sSup (w '' S) + 2 * C) / 2 < sSup (w '' S) := by linarith
  obtain ⟨_, ⟨y, hyS, rfl⟩, hy⟩ :=
    exists_lt_of_lt_csSup ⟨w b, mem_image_of_mem w hbS⟩ hmid
  have hyweight : 2 * C < w y := by linarith
  have hypos : 0 < √(g y) :=
    pos_of_mul_pos_right (lt_of_le_of_lt (by positivity) hyweight)
      (sub_nonneg.mpr (mem_closedBall.mp hyS))
  have hscale : C / √(g y) < (r - dist (f y) o) / 2 := by
    apply (div_lt_iff₀ hypos).2
    dsimp only [w] at hyweight
    nlinarith
  refine ⟨y, Real.sqrt_pos.1 hypos, by linarith, fun z hz ↦ ?_⟩
  by_contra! h
  have hroot : 2 * √(g y) < √(g z) :=
    (Real.lt_sqrt (by positivity)).2 (by nlinarith [Real.sq_sqrt (Real.sqrt_pos.1 hypos).le])
  have hdz : dist (f z) o < dist (f y) o + C / √(g y) := by
    linarith [dist_triangle (f z) (f y) o, mem_ball.1 hz]
  have hdzr : dist (f z) o < r := by linarith [mem_closedBall.mp hyS]
  have hzw : sSup (w '' S) < w z := by
    calc
      sSup (w '' S) < 2 * w y - 2 * C := by linarith
      _ = (r - dist (f y) o - C / √(g y)) * (2 * √(g y)) := by
        dsimp only [w]
        nlinarith [div_mul_cancel₀ C hypos.ne']
      _ ≤ (r - dist (f z) o) * (2 * √(g y)) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ < w z := mul_lt_mul_of_pos_left hroot (sub_pos.mpr hdzr)
  exact hzw.not_ge (le_csSup hbounded (mem_image_of_mem w (mem_closedBall.mpr hdzr.le)))

variable [TopologicalSpace X]

/-- If the supremum of `g` on the preimage of the half-radius ball is at least
`16 * C ^ 2 / R ^ 2`, there is a point `y` where `g y = C ^ 2 / s ^ 2` for a positive
scale `s` inside the full ball, and `g ≤ 4 * g y` on the preimage of the ball of radius
`s` about `f y`. Only preimages of closed balls of radii strictly less than `R` are
assumed compact. -/
theorem exists_pointPicking_of_isCompact_preimage (hR : 0 < R) (hC : C ≠ 0)
    (hK : ∀ r < R, IsCompact (f ⁻¹' closedBall o r))
    (hg : ∀ r < R, UpperSemicontinuousOn g (f ⁻¹' closedBall o r))
    (hsup : 16 * C ^ 2 / R ^ 2 ≤ ⨆ x ∈ f ⁻¹' ball o (R / 2), g x) :
    ∃ y s, 0 < s ∧ s < R - dist (f y) o ∧
      (∀ z, f z ∈ ball (f y) s → g z ≤ 4 * g y) ∧ g y = C ^ 2 / s ^ 2 := by
  have hC' : 0 < |C| := abs_pos.2 hC
  have hpos : 0 < 16 * C ^ 2 / R ^ 2 := by positivity
  rcases (f ⁻¹' ball o (R / 2)).eq_empty_or_nonempty with hempty | hne
  · exact False.elim (hpos.not_ge (by simpa [hempty] using hsup))
  have hn : (f ⁻¹' closedBall o (R / 2)).Nonempty :=
    hne.mono (preimage_mono ball_subset_closedBall)
  have hhalf : R / 2 < R := by linarith
  obtain ⟨x, hx, hxmax⟩ := (hg _ hhalf).exists_isMaxOn hn (hK _ hhalf)
  have hbound : 16 * C ^ 2 / R ^ 2 ≤ max 0 (g x) :=
    hsup.trans (Real.iSup_le (fun z ↦ Real.iSup_le (fun hz ↦
      (hxmax (ball_subset_closedBall hz)).trans (le_max_right _ _)) (le_max_left _ _))
        (le_max_left _ _))
  have hxg : 16 * C ^ 2 / R ^ 2 ≤ g x := (le_max_iff.mp hbound).resolve_left hpos.not_ge
  have hxpos : 0 < g x := hpos.trans_le hxg
  let s (y : X) := |C| / √(g y)
  have hs {y : X} (hy : 0 < g y) : 0 < s y := div_pos hC' (Real.sqrt_pos.2 hy)
  have hxR : dist (f x) o + 2 * s x ≤ R := by
    have hxR' : dist (f x) o ≤ R / 2 := hx
    have hroot : (4 * |C| / R) ≤ √(g x) := Real.le_sqrt_of_sq_le (by
      norm_num [div_pow, mul_pow, sq_abs]
      exact hxg)
    have hscale : s x ≤ R / 4 := by
      dsimp [s]
      apply (div_le_iff₀ (Real.sqrt_pos.2 hxpos)).2
      nlinarith [(div_le_iff₀ hR).1 hroot]
    linarith
  suffices H : ∃ y, 0 < g y ∧ dist (f y) o + 2 * s y ≤ R ∧
      ∀ z, f z ∈ ball (f y) (s y) → g z ≤ 4 * g y by
    obtain ⟨y, hy, hyR, hgood⟩ := H
    refine ⟨y, s y, hs hy, by linarith [hs hy], hgood, ?_⟩
    have hsq : s y ^ 2 = C ^ 2 / g y := by
      dsimp only [s]
      rw [div_pow, sq_abs, Real.sq_sqrt hy.le]
    rw [eq_div_iff (pow_ne_zero _ (hs hy).ne'), hsq, mul_div_cancel₀ _ hy.ne']
  by_cases hgood : ∀ z, f z ∈ ball (f x) (s x) → g z ≤ 4 * g x
  · exact ⟨x, hxpos, hxR, hgood⟩
  push Not at hgood
  obtain ⟨z, hz, hzg⟩ := hgood
  have hxz : 2 * √(g x) < √(g z) :=
    (Real.lt_sqrt (by positivity)).2 (by nlinarith [Real.sq_sqrt hxpos.le])
  have hzpos : 0 < g z := by linarith
  have hscale : 2 * s z < s x := by
    dsimp [s]
    rw [← mul_div_assoc, div_lt_div_iff₀ (Real.sqrt_pos.2 hzpos) (Real.sqrt_pos.2 hxpos)]
    nlinarith [mul_lt_mul_of_pos_left hxz hC']
  have hzR : dist (f z) o + 2 * s z < R := by
    linarith [mem_ball.1 hz, dist_triangle (f z) (f x) o]
  exact exists_pointPicking_of_strict_margin
    (fun r hr ↦ (hg r hr).bddAbove_of_isCompact (hK r hr)) hzpos hzR

end TauCeti
