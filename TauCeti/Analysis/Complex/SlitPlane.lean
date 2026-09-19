/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic

/-!
# Geometry of the complex slit plane

The quotient `z₂ / z₁` of two points of an open half-plane through the origin is never a
nonpositive real, so it lies in `Complex.slitPlane`. The half-plane is encoded by a normal
direction `a`: its members are the `z` with `0 < (conj a * z).re`. Specializations to the
four axis-aligned half-planes cover the common cases.

The module also records a locally uniform lower bound for the distance from a point of the slit
plane to the closed negative half-axis.

These criteria feed logarithm evaluations of index integrals: a curve piece confined to a
half-plane about the winding point has slit-compatible chord ratios, so its index integral
is a principal logarithm.

## Main declarations

* `TauCeti.div_mem_slitPlane_of_re_conj_mul_pos`
* `TauCeti.div_mem_slitPlane_of_re_pos`, `…_of_re_neg`, `…_of_im_pos`, `…_of_im_neg`
* `TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add`
-/

public section

open Complex
open scoped NNReal

namespace TauCeti

/-- The ratio of two members of an open half-plane through the origin lies in the slit
plane. The half-plane with normal direction `a` is `{z | 0 < (conj a * z).re}`; degenerate
`a` admits no members, so no nonvanishing hypothesis is needed. -/
theorem div_mem_slitPlane_of_re_conj_mul_pos {a z₁ z₂ : ℂ}
    (h₁ : 0 < ((starRingEnd ℂ) a * z₁).re) (h₂ : 0 < ((starRingEnd ℂ) a * z₂).re) :
    z₂ / z₁ ∈ slitPlane := by
  have hz₁ : z₁ ≠ 0 := by rintro rfl; simp at h₁
  by_contra hmem
  rw [mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hmem
  obtain ⟨hre, him⟩ := hmem
  have heq : z₂ / z₁ = (((z₂ / z₁).re : ℝ) : ℂ) := Complex.ext (by simp) (by simpa using him)
  have hz₂ : z₂ = (((z₂ / z₁).re : ℝ) : ℂ) * z₁ := by
    rw [← heq, div_mul_cancel₀ _ hz₁]
  have hkey : ((starRingEnd ℂ) a) * ((((z₂ / z₁).re : ℝ) : ℂ) * z₁) =
      (((z₂ / z₁).re : ℝ) : ℂ) * ((starRingEnd ℂ) a * z₁) := by ring
  rw [hz₂, hkey, Complex.re_ofReal_mul] at h₂
  nlinarith

/-- Two points in the right half-plane have their ratio in the slit plane. -/
theorem div_mem_slitPlane_of_re_pos {z₁ z₂ : ℂ} (h₁ : 0 < z₁.re) (h₂ : 0 < z₂.re) :
    z₂ / z₁ ∈ slitPlane :=
  div_mem_slitPlane_of_re_conj_mul_pos (a := 1) (by simpa) (by simpa)

/-- Two points in the left half-plane have their ratio in the slit plane. -/
theorem div_mem_slitPlane_of_re_neg {z₁ z₂ : ℂ} (h₁ : z₁.re < 0) (h₂ : z₂.re < 0) :
    z₂ / z₁ ∈ slitPlane :=
  div_mem_slitPlane_of_re_conj_mul_pos (a := -1)
    (by simpa using neg_pos.mpr h₁) (by simpa using neg_pos.mpr h₂)

/-- Two points in the upper half-plane have their ratio in the slit plane. -/
theorem div_mem_slitPlane_of_im_pos {z₁ z₂ : ℂ} (h₁ : 0 < z₁.im) (h₂ : 0 < z₂.im) :
    z₂ / z₁ ∈ slitPlane :=
  div_mem_slitPlane_of_re_conj_mul_pos (a := Complex.I)
    (by simpa [Complex.mul_re]) (by simpa [Complex.mul_re])

/-- Two points in the lower half-plane have their ratio in the slit plane. -/
theorem div_mem_slitPlane_of_im_neg {z₁ z₂ : ℂ} (h₁ : z₁.im < 0) (h₂ : z₂.im < 0) :
    z₂ / z₁ ∈ slitPlane :=
  div_mem_slitPlane_of_re_conj_mul_pos (a := -Complex.I)
    (by simpa [Complex.mul_re] using neg_pos.mpr h₁)
    (by simpa [Complex.mul_re] using neg_pos.mpr h₂)

/-- On a small ball around a point of the slit plane, the distance from `w` to the point `-x`
of the closed negative half-axis is bounded below by a fixed multiple of `1 + x`. -/
theorem exists_pos_forall_mem_ball_mul_one_add_le_norm_add {z : ℂ} (hz : z ∈ slitPlane) :
    ∃ c > 0, ∀ w ∈ Metric.ball z c, ∀ x : ℝ≥0, c * (1 + (x : ℝ)) ≤ ‖w + ((x : ℝ) : ℂ)‖ := by
  -- First a bound at `z` itself, then halve the constant to absorb the displacement `w - z`.
  obtain ⟨c, hc, hzc⟩ : ∃ c > 0, ∀ x : ℝ, 0 ≤ x → c * (1 + x) ≤ ‖z + (x : ℂ)‖ := by
    have hre (x : ℝ) : z.re + x ≤ ‖z + (x : ℂ)‖ := by
      simpa using Complex.re_le_norm (z + (x : ℂ))
    rcases mem_slitPlane_iff.mp hz with hpos | him
    · refine ⟨min z.re 1, lt_min hpos one_pos, fun x hx => (hre x).trans' ?_⟩
      nlinarith [min_le_left z.re 1, min_le_right z.re 1,
        mul_nonneg (sub_nonneg.2 (min_le_right z.re 1)) hx]
    · have hy : 0 < |z.im| := abs_pos.mpr him
      have hu : 0 ≤ |z.re| := abs_nonneg _
      refine ⟨min (|z.im| / (2 * |z.re| + 2)) (1 / 4), lt_min (by positivity) (by norm_num),
        fun x hx => ?_⟩
      rcases le_or_gt x (2 * |z.re| + 1) with hxu | hxu
      · have him_le : |z.im| ≤ ‖z + (x : ℂ)‖ := by
          simpa using Complex.abs_im_le_norm (z + (x : ℂ))
        calc min (|z.im| / (2 * |z.re| + 2)) (1 / 4) * (1 + x)
            ≤ |z.im| / (2 * |z.re| + 2) * (2 * |z.re| + 2) :=
              mul_le_mul (min_le_left _ _) (by linarith) (by linarith) (by positivity)
          _ = |z.im| := div_mul_cancel₀ _ (by positivity)
          _ ≤ ‖z + (x : ℂ)‖ := him_le
      · refine (hre x).trans' ?_
        nlinarith [min_le_right (|z.im| / (2 * |z.re| + 2)) (1 / 4), neg_abs_le z.re,
          lt_min_iff.mp (lt_min (by positivity : (0 : ℝ) < |z.im| / (2 * |z.re| + 2))
            (by norm_num : (0 : ℝ) < 1 / 4))]
  refine ⟨c / 2, half_pos hc, fun w hw x => ?_⟩
  have hwz : ‖z - w‖ < c / 2 := by rw [← dist_eq_norm, dist_comm]; exact hw
  have htri : ‖z + ((x : ℝ) : ℂ)‖ ≤ ‖w + ((x : ℝ) : ℂ)‖ + ‖z - w‖ := by
    calc
      ‖z + ((x : ℝ) : ℂ)‖ = ‖(w + ((x : ℝ) : ℂ)) + (z - w)‖ := by congr 1; ring
      _ ≤ ‖w + ((x : ℝ) : ℂ)‖ + ‖z - w‖ := norm_add_le _ _
  nlinarith [hzc x x.coe_nonneg, x.coe_nonneg]

end TauCeti

end
