/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Norm bounds for nonnegative translations in complex sectors

For a complex number `s` separated in argument from the negative real axis and a nonnegative
real `t`, the norm of the translate `s + t` is bounded below by a fixed multiple of `‖s‖ + t`:
`√c * (‖s‖ + t) ≤ ‖s + t‖` whenever `(2c - 1) ‖s‖ ≤ re s` and `0 ≤ c ≤ 1`
(`Complex.sqrt_mul_norm_add_le_norm_add_ofReal`), which sharpens `c * (‖s‖ + t) ≤ ‖s + t‖`
(`Complex.mul_norm_add_le_norm_add_ofReal`). More sharply,
`cos (arg z / 2) * (‖z‖ + t) ≤ ‖z + t‖` for every `z : ℂ` and `t : ℝ`, and on the closed sector
`|arg z| ≤ π - δ` with `0 ≤ δ` the sharp constant is `sin (δ / 2)`
(`Complex.sin_half_mul_norm_add_le_norm_add_ofReal_of_abs_arg_le`), strengthening the squared
constant `(1 - cos δ) / 2 = sin (δ / 2) ^ 2` for `t ≥ 0`
(`Complex.mul_norm_add_le_norm_add_ofReal_of_abs_arg_le`). For `z` in the sector
`Re z ≤ c ‖z‖`, `c < 1`, around the negative real axis,
`(1 - max c (-1)) / 2 * (t + ‖z‖) ≤ ‖t - z‖`. These inequalities control reciprocal kernels in
sectorial and Stieltjes integrals and resolvent symbols. A nonzero point of such a sector, with
`0 < δ`, lies in the slit plane, and every sector `{z : ℂ | |arg z| < α ∧ r < ‖z‖}` is
preconnected (`Complex.isPreconnected_setOf_abs_arg_lt_and_lt_norm`).
-/

public section

open Complex Real

namespace Complex

/-- If `(2c - 1) ‖s‖ ≤ re s` with `0 ≤ c ≤ 1`, then `√c * (‖s‖ + t) ≤ ‖s + t‖` for every
nonnegative real `t`. This sharpens `Complex.mul_norm_add_le_norm_add_ofReal`. -/
theorem sqrt_mul_norm_add_le_norm_add_ofReal {s : ℂ} {c t : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (hs : (2 * c - 1) * ‖s‖ ≤ s.re) :
    Real.sqrt c * (‖s‖ + t) ≤ ‖s + t‖ := by
  have hsq : ‖s + t‖ ^ 2 = ‖s‖ ^ 2 + 2 * t * s.re + t ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  have h : c * (‖s‖ + t) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg (‖s‖ - t)),
      mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * t)]
  have h2 : (Real.sqrt c * (‖s‖ + t)) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hc]
    exact h
  nlinarith [norm_nonneg (s + t), Real.sqrt_nonneg c, norm_nonneg s]

/-- If `(2c - 1) ‖s‖ ≤ re s` with `0 ≤ c ≤ 1`, then `c * (‖s‖ + t) ≤ ‖s + t‖` for every
nonnegative real `t`. -/
theorem mul_norm_add_le_norm_add_ofReal {s : ℂ} {c t : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (hs : (2 * c - 1) * ‖s‖ ≤ s.re) :
    c * (‖s‖ + t) ≤ ‖s + t‖ := by
  refine le_trans ?_ (sqrt_mul_norm_add_le_norm_add_ofReal hc hc1 ht hs)
  have hle : c ≤ Real.sqrt c := by
    rw [Real.le_sqrt hc hc]
    nlinarith
  exact mul_le_mul_of_nonneg_right hle (by positivity)

/-- On the closed sector `|arg s| ≤ π - δ`, translation by a nonnegative real `t` satisfies
`((1 - cos δ) / 2) * (‖s‖ + t) ≤ ‖s + t‖`. -/
theorem mul_norm_add_le_norm_add_ofReal_of_abs_arg_le {s : ℂ} {δ t : ℝ}
    (hδ : 0 < δ) (hs : |s.arg| ≤ Real.pi - δ) (ht : 0 ≤ t) :
    ((1 - Real.cos δ) / 2) * (‖s‖ + t) ≤ ‖s + t‖ := by
  apply mul_norm_add_le_norm_add_ofReal
  · linarith [Real.cos_le_one δ]
  · linarith [Real.neg_one_le_cos δ]
  · exact ht
  · have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg s.arg)
      (by linarith : Real.pi - δ ≤ Real.pi) hs
    rw [Real.cos_abs, Real.cos_pi_sub] at hcos
    have h := mul_le_mul_of_nonneg_left hcos (norm_nonneg s)
    rw [norm_mul_cos_arg] at h
    nlinarith

/-- On the sector `Re z ≤ c ‖z‖`, the difference `t - z` with a nonnegative real `t` satisfies
`(1 - max c (-1)) / 2 * (t + ‖z‖) ≤ ‖t - z‖`. For `c < 1` this keeps `t - z` away from `0`; for
`c ≥ 1` the left side is nonpositive. -/
theorem mul_add_norm_le_norm_ofReal_sub {z : ℂ} {c t : ℝ} (ht : 0 ≤ t) (hz : z.re ≤ c * ‖z‖) :
    (1 - max c (-1)) / 2 * (t + ‖z‖) ≤ ‖(t : ℂ) - z‖ := by
  rcases le_or_gt 1 c with hc | hc
  · have : (1 - max c (-1)) / 2 ≤ 0 := by linarith [le_max_left c (-1)]
    nlinarith [norm_nonneg ((t : ℂ) - z), norm_nonneg z]
  have h := mul_norm_add_le_norm_add_ofReal (s := -z) (c := (1 - max c (-1)) / 2)
    (by linarith [max_lt hc (show (-1 : ℝ) < 1 by norm_num)]) (by linarith [le_max_right c (-1)])
    ht (by
      rw [norm_neg, neg_re]
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left c (-1)) (norm_nonneg z)])
  rwa [norm_neg, neg_add_eq_sub, add_comm ‖z‖ t] at h

/-- For every complex `z` and real `t`,
`‖z + t‖² - (cos (arg z / 2) * (‖z‖ + t))² = (sin (arg z / 2) * (‖z‖ - t))²`. -/
theorem norm_add_ofReal_sq_sub_cos_half_arg_sq (z : ℂ) (t : ℝ) :
    ‖z + (t : ℂ)‖ ^ 2 - (Real.cos (z.arg / 2) * (‖z‖ + t)) ^ 2 =
      (Real.sin (z.arg / 2) * (‖z‖ - t)) ^ 2 := by
  have hsq : ‖z + (t : ℂ)‖ ^ 2 = ‖z‖ ^ 2 + 2 * t * z.re + t ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  have hre : z.re = ‖z‖ * (2 * Real.cos (z.arg / 2) ^ 2 - 1) := by
    rw [← norm_mul_cos_arg z, ← Real.cos_two_mul]
    ring_nf
  have hcs := Real.sin_sq_add_cos_sq (z.arg / 2)
  rw [hsq, hre]
  linear_combination -((‖z‖ - t) ^ 2) * hcs

/-- Because `arg z ∈ (-π, π]`, the half-angle cosine `cos (arg z / 2)` is always nonnegative. -/
theorem cos_half_arg_nonneg (z : ℂ) : 0 ≤ Real.cos (z.arg / 2) :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [neg_pi_lt_arg z], by linarith [arg_le_pi z]⟩

/-- The half-angle cosine `cos (arg z / 2)` is strictly positive iff `z` does not lie on the
negative real axis (`arg z ≠ π`). -/
theorem cos_half_arg_pos_iff {z : ℂ} : 0 < Real.cos (z.arg / 2) ↔ z.arg ≠ Real.pi := by
  refine ⟨fun h hpi ↦ ?_, fun hne ↦ ?_⟩
  · rw [hpi, Real.cos_pi_div_two] at h
    exact lt_irrefl 0 h
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_pi_lt_arg z],
      by linarith [lt_of_le_of_ne (arg_le_pi z) hne]⟩

/-- Every point of the slit plane has `0 < cos (arg z / 2)`. -/
theorem cos_half_arg_pos {z : ℂ} (hz : z ∈ slitPlane) : 0 < Real.cos (z.arg / 2) :=
  cos_half_arg_pos_iff.mpr (mem_slitPlane_iff_arg.mp hz).1

/-- For every complex `z` and real `t`, `|cos (arg z / 2) * (‖z‖ + t)| ≤ ‖z + t‖`. -/
theorem abs_cos_half_arg_mul_norm_add_le_norm_add_ofReal (z : ℂ) (t : ℝ) :
    |Real.cos (z.arg / 2) * (‖z‖ + t)| ≤ ‖z + (t : ℂ)‖ := by
  have hsq : (Real.cos (z.arg / 2) * (‖z‖ + t)) ^ 2 ≤ ‖z + (t : ℂ)‖ ^ 2 := by
    linarith [norm_add_ofReal_sq_sub_cos_half_arg_sq z t,
      sq_nonneg (Real.sin (z.arg / 2) * (‖z‖ - t))]
  simpa only [abs_norm] using sq_le_sq.mp hsq

/-- Sharp half-angle translation lower bound: `cos (arg z / 2) * (‖z‖ + t) ≤ ‖z + t‖` for every
complex `z` and real `t`. -/
theorem cos_half_arg_mul_norm_add_le_norm_add_ofReal (z : ℂ) (t : ℝ) :
    Real.cos (z.arg / 2) * (‖z‖ + t) ≤ ‖z + (t : ℂ)‖ :=
  (le_abs_self _).trans (abs_cos_half_arg_mul_norm_add_le_norm_add_ofReal z t)

/-- On the closed sector `|arg z| ≤ π - δ` with `0 ≤ δ`, the half-angle cosine satisfies
`sin (δ / 2) ≤ cos (arg z / 2)`. -/
theorem sin_half_le_cos_half_arg_of_abs_arg_le {z : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hs : |z.arg| ≤ Real.pi - δ) :
    Real.sin (δ / 2) ≤ Real.cos (z.arg / 2) := by
  have hle : |z.arg / 2| ≤ Real.pi / 2 - δ / 2 := by
    rw [abs_div, abs_two]
    linarith
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (z.arg / 2))
    (by linarith [Real.pi_pos]) hle
  rwa [Real.cos_abs, Real.cos_pi_div_two_sub] at hcos

/-- On the closed sector `|arg z| ≤ π - δ` with `0 ≤ δ`, every real translate `z + t` satisfies
`sin (δ / 2) * (‖z‖ + t) ≤ ‖z + t‖`. -/
theorem sin_half_mul_norm_add_le_norm_add_ofReal_of_abs_arg_le {z : ℂ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hs : |z.arg| ≤ Real.pi - δ) (t : ℝ) :
    Real.sin (δ / 2) * (‖z‖ + t) ≤ ‖z + (t : ℂ)‖ := by
  have hδπ : δ ≤ Real.pi := by linarith [abs_nonneg z.arg]
  have hsin : 0 ≤ Real.sin (δ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
  rcases le_or_gt 0 (‖z‖ + t) with hzt | hzt
  · exact (mul_le_mul_of_nonneg_right (sin_half_le_cos_half_arg_of_abs_arg_le hδ hs) hzt).trans
      (cos_half_arg_mul_norm_add_le_norm_add_ofReal z t)
  · exact (mul_nonpos_of_nonneg_of_nonpos hsin hzt.le).trans (norm_nonneg _)

/-- A nonzero complex number with `|arg s| < π` lies in the slit plane. -/
theorem mem_slitPlane_of_abs_arg_lt {s : ℂ} (hs : |s.arg| < Real.pi) (hs0 : s ≠ 0) :
    s ∈ slitPlane :=
  mem_slitPlane_iff_arg.mpr ⟨fun h ↦ by rw [h, abs_of_pos Real.pi_pos] at hs; exact hs.false, hs0⟩

/-- A nonzero complex number in the closed sector `|arg s| ≤ π - δ`, with `0 < δ`, lies in the
slit plane. -/
theorem mem_slitPlane_of_abs_arg_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : |s.arg| ≤ Real.pi - δ)
    (hs0 : s ≠ 0) : s ∈ slitPlane :=
  mem_slitPlane_of_abs_arg_lt (by linarith) hs0

/-- Every sector `{z : ℂ | |arg z| < α ∧ r < ‖z‖}` is preconnected. -/
theorem isPreconnected_setOf_abs_arg_lt_and_lt_norm {α r : ℝ} :
    IsPreconnected {z : ℂ | |z.arg| < α ∧ r < ‖z‖} := by
  let φ : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hφ : Continuous φ := by fun_prop
  -- Realize the sector as the continuous polar image of `(Ici 0 ∩ Ioi r) ×ˢ Ioo (-α) α`.
  have himg : φ '' ((Set.Ici 0 ∩ Set.Ioi r) ×ˢ Set.Ioo (-α) α) =
      {z : ℂ | |z.arg| < α ∧ r < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨ρ, θ⟩, ⟨⟨hρ0, hrρ⟩, hθ⟩, rfl⟩
      have hnorm : ‖φ (ρ, θ)‖ = ρ := by
        simp [φ, abs_of_nonneg hρ0]
      refine ⟨?_, by rwa [hnorm]⟩
      rcases lt_or_ge Real.pi α with hα | hα
      · exact (abs_arg_le_pi _).trans_lt hα
      · rcases hρ0.eq_or_lt with rfl | hρ_pos
        · simp only [φ, ofReal_zero, zero_mul, arg_zero, abs_zero]
          linarith [hθ.1, hθ.2]
        · have harg : (φ (ρ, θ)).arg = θ := by
            rw [arg_ofReal_mul hρ_pos _, arg_exp_mul_I, toIocMod_eq_self]
            exact ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
          rw [harg]
          exact abs_lt.mpr hθ
    · rintro ⟨harg, hnorm⟩
      exact ⟨(‖z‖, z.arg), ⟨⟨norm_nonneg z, hnorm⟩, abs_lt.mp harg⟩, norm_mul_exp_arg_mul_I z⟩
  rw [← himg]
  exact ((Set.ordConnected_Ici.inter Set.ordConnected_Ioi).isPreconnected.prod
    isPreconnected_Ioo).image φ hφ.continuousOn

end Complex
