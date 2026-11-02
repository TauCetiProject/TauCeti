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
four axis-aligned half-planes cover the common cases. A relative displacement smaller than
the distance to a pole also gives a slit-plane quotient.

Translating a point of the slit plane by a nonnegative real number keeps it in the slit plane,
and translating a point of `slitPlane ∪ {0}` by a positive one lands in the slit plane.
The module also records a locally uniform lower bound for the distance from a point of the slit
plane to the closed negative half-axis. This bound locally dominates slit-plane kernels and thus
supports differentiation and holomorphy arguments for parameter-dependent Stieltjes integrals.
For `x` in the slit plane, `‖t + x‖` grows at least linearly in the real number `t ≥ 0`; this
controls integrands of the form `(t + x) ^ s` over `t ∈ (0, ∞)`, such as those of Carlson's
symmetric elliptic integrals.
For `x ∈ slitPlane ∪ {0}`, the quotient `a / (t + x)` is continuous for `t > 0` and the term
`x / (t + x) · t` stays bounded.

These criteria feed logarithm evaluations of index integrals: a curve piece confined to a
half-plane about the winding point has slit-compatible chord ratios, so its index integral
is a principal logarithm.

## Main declarations

* `TauCeti.div_sub_mem_slitPlane_of_dist_lt_dist`
* `TauCeti.div_mem_slitPlane_of_re_conj_mul_pos`
* `TauCeti.div_mem_slitPlane_of_re_pos`, `…_of_re_neg`, `…_of_im_pos`, `…_of_im_neg`
* `TauCeti.ofReal_add_mem_slitPlane`, `TauCeti.ofReal_add_mem_slitPlane_of_mem_union`
* `TauCeti.ofReal_mem_slitPlane_union_zero`
* `TauCeti.exists_pos_forall_mem_ball_mul_one_add_le_norm_add`
* `TauCeti.exists_pos_mul_one_add_le_norm_ofReal_add`
* `TauCeti.exists_norm_div_ofReal_add_mul_le`, `TauCeti.continuousOn_div_ofReal_add`
* `TauCeti.exists_norm_inv_ofReal_add_le` -- `(t + p)⁻¹ = O((1 + t)⁻¹)` for `p ∈ slitPlane`
-/

public section

open Complex
open scoped NNReal

namespace TauCeti

/-- The quotient under the proximity inequality lies in the slit plane. -/
theorem div_sub_mem_slitPlane_of_dist_lt_dist
    {x y w : ℂ} (h : dist y x < dist x w) :
    (y - w) / (x - w) ∈ slitPlane := by
  have hne : x - w ≠ 0 := sub_ne_zero.mpr
    (dist_pos.mp (lt_of_le_of_lt dist_nonneg h))
  have hsub : (y - w) / (x - w) - 1 = (y - x) / (x - w) := by
    field_simp
    ring
  apply Complex.ball_one_subset_slitPlane
  rw [Metric.mem_ball, dist_eq_norm, hsub, norm_div, div_lt_one (norm_pos_iff.mpr hne)]
  simpa only [dist_eq_norm] using h


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

/-- Translating a point of the slit plane by a nonnegative real number keeps it in the slit
plane. -/
theorem ofReal_add_mem_slitPlane {z : ℂ} (hz : z ∈ slitPlane) {t : ℝ} (ht : 0 ≤ t) :
    (t : ℂ) + z ∈ slitPlane := by
  rcases mem_slitPlane_iff.mp hz with h | h
  · exact mem_slitPlane_iff.mpr (Or.inl (by
      simp only [Complex.add_re, Complex.ofReal_re]; linarith))
  · exact mem_slitPlane_iff.mpr (Or.inr (by simpa using h))

/-- Translating a point of `slitPlane ∪ {0}` by a positive real number lands in the slit
plane. -/
theorem ofReal_add_mem_slitPlane_of_mem_union {z : ℂ} (hz : z ∈ slitPlane ∪ {0}) {t : ℝ}
    (ht : 0 < t) : (t : ℂ) + z ∈ slitPlane := by
  rcases hz with hz | hz
  · exact ofReal_add_mem_slitPlane hz ht.le
  · rw [Set.mem_singleton_iff.mp hz, add_zero]
    exact ofReal_mem_slitPlane.mpr ht

/-- A nonnegative real number lies in `slitPlane ∪ {0}`. -/
theorem ofReal_mem_slitPlane_union_zero {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) ∈ slitPlane ∪ {0} := by
  rcases hx.eq_or_lt with h | h
  · exact Or.inr (by simp [← h])
  · exact Or.inl (ofReal_mem_slitPlane.mpr h)

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
    · have _ : 0 < |z.im| := abs_pos.mpr him
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

/-- For `x ∈ slitPlane`, `‖t + x‖` grows at least linearly: `c (1 + t) ≤ ‖t + x‖` for `t ≥ 0`. -/
theorem exists_pos_mul_one_add_le_norm_ofReal_add {x : ℂ} (hx : x ∈ slitPlane) :
    ∃ c, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → c * (1 + t) ≤ ‖(t : ℂ) + x‖ := by
  obtain ⟨c, hc, h⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hx
  refine ⟨c, hc, fun t ht => ?_⟩
  rw [add_comm (t : ℂ)]
  exact h x (Metric.mem_ball_self hc) ⟨t, ht⟩

/-- For `x ∈ slitPlane ∪ {0}`, the term `x / (t + x) · t` is bounded for `t > 0`. -/
theorem exists_norm_div_ofReal_add_mul_le {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) :
    ∃ C, 0 ≤ C ∧ ∀ t : ℝ, 0 < t → ‖x / ((t : ℂ) + x) * t‖ ≤ C := by
  rcases hx with hx | hx
  · obtain ⟨c, hc, h⟩ := exists_pos_mul_one_add_le_norm_ofReal_add hx
    refine ⟨‖x‖ / c, by positivity, fun t ht => ?_⟩
    have hpos : 0 < ‖(t : ℂ) + x‖ := lt_of_lt_of_le (by positivity) (h t ht.le)
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg ht.le, div_mul_eq_mul_div,
      div_le_div_iff₀ hpos hc]
    have := h t ht.le
    nlinarith [norm_nonneg x]
  · exact ⟨0, le_rfl, fun t _ => by simp [Set.mem_singleton_iff.mp hx]⟩

/-- For `x ∈ slitPlane ∪ {0}` and any `a : ℂ`, the quotient `a / (t + x)` is continuous in the
real variable `t > 0`. -/
theorem continuousOn_div_ofReal_add {x : ℂ} (hx : x ∈ slitPlane ∪ {0}) (a : ℂ) :
    ContinuousOn (fun t : ℝ => a / ((t : ℂ) + x)) (Set.Ioi 0) := fun _ ht =>
  (continuousAt_const.div (Complex.continuous_ofReal.add continuous_const).continuousAt
    (slitPlane_ne_zero (ofReal_add_mem_slitPlane_of_mem_union hx ht))).continuousWithinAt

/-- For `p ∈ slitPlane`, the reciprocal `(t + p)⁻¹` is `O((1 + t)⁻¹)` uniformly in `t ≥ 0`. -/
theorem exists_norm_inv_ofReal_add_le {p : ℂ} (hp : p ∈ slitPlane) :
    ∃ C, 0 < C ∧ ∀ t : ℝ, 0 ≤ t → ‖((t : ℂ) + p)⁻¹‖ ≤ C * (1 + t)⁻¹ := by
  obtain ⟨c, hc, h⟩ := exists_pos_mul_one_add_le_norm_ofReal_add hp
  refine ⟨c⁻¹, inv_pos.mpr hc, fun t ht => ?_⟩
  rw [norm_inv, ← mul_inv]
  exact inv_anti₀ (by positivity) (h t ht)

end TauCeti

end
