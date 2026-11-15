/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Norm and argument bounds in complex sectors

For a complex number `s` separated in argument from the negative real axis and a nonnegative
real `t`, the norm of the translate `s + t` is bounded below by a fixed multiple of `‖s‖ + t`:
`c * (‖s‖ + t) ≤ ‖s + t‖`, where `0 ≤ c ≤ 1` depends only on the angular separation. On the
sector `|arg s| ≤ π - δ` one may take `c = (1 - cos δ) / 2`. These inequalities control
reciprocal kernels in sectorial integrals. A nonzero point of such a sector, with `0 < δ`, lies in
the slit plane.

For open discs centered in a sector, the tangent angle from the origin to `Metric.ball c r` is
controlled by `r / ‖c‖`: when `0 < δ ≤ π / 2` and `r ≤ ‖c‖ * sin δ` (with `arg c ± δ` avoiding the
branch cut), every `z ∈ Metric.ball c r` satisfies `|arg z - arg c| < δ`
(`Complex.abs_arg_sub_lt_of_mem_ball`), placing the whole disc inside an open sector
(`Complex.arg_mem_Ioo_of_mem_ball`).
-/

public section

open Complex Real

namespace Complex

/-- If `(2c - 1) ‖s‖ ≤ re s` with `0 ≤ c ≤ 1`, then `c * (‖s‖ + t) ≤ ‖s + t‖` for every
nonnegative real `t`. -/
theorem mul_norm_add_le_norm_add_ofReal {s : ℂ} {c t : ℝ}
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (ht : 0 ≤ t)
    (hs : (2 * c - 1) * ‖s‖ ≤ s.re) :
    c * (‖s‖ + t) ≤ ‖s + t‖ := by
  have hsq : ‖s + t‖ ^ 2 = ‖s‖ ^ 2 + 2 * t * s.re + t ^ 2 := by
    simp only [Complex.sq_norm, normSq_apply, add_re, ofReal_re, add_im, ofReal_im, add_zero]
    ring
  have h : c * (‖s‖ + t) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc1) (sq_nonneg (‖s‖ - t)),
      mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * t)]
  have hc2 : c ^ 2 ≤ c := by nlinarith
  have h2 : (c * (‖s‖ + t)) ^ 2 ≤ ‖s + t‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc2 (sq_nonneg (‖s‖ + t))]
  nlinarith [norm_nonneg (s + t)]

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

/-- A nonzero complex number with `|arg s| < π` lies in the slit plane. -/
theorem mem_slitPlane_of_abs_arg_lt {s : ℂ} (hs : |s.arg| < Real.pi) (hs0 : s ≠ 0) :
    s ∈ slitPlane :=
  mem_slitPlane_iff_arg.mpr ⟨fun h ↦ by rw [h, abs_of_pos Real.pi_pos] at hs; exact hs.false, hs0⟩

/-- A nonzero complex number in the closed sector `|arg s| ≤ π - δ`, with `0 < δ`, lies in the
slit plane. -/
theorem mem_slitPlane_of_abs_arg_le {s : ℂ} {δ : ℝ} (hδ : 0 < δ) (hs : |s.arg| ≤ Real.pi - δ)
    (hs0 : s ≠ 0) : s ∈ slitPlane :=
  mem_slitPlane_of_abs_arg_lt (by linarith) hs0

/-- **Sharp tangent-angle bound on `ball 1 (sin δ)`.** If `0 < δ ≤ π / 2` and `‖u‖ < sin δ`, then
`|(1 + u).arg| < δ`. -/
theorem abs_arg_one_add_lt_of_norm_lt_sin {u : ℂ} {δ : ℝ}
    (hδ₀ : 0 < δ) (hδ₁ : δ ≤ Real.pi / 2) (hu : ‖u‖ < Real.sin δ) :
    |(1 + u).arg| < δ := by
  have hre_lt : |u.re| < 1 :=
    (abs_re_le_norm u).trans_lt (hu.trans_le (Real.sin_le_one δ))
  have hre_pos : 0 < (1 + u).re := by simp; linarith [(abs_lt.mp hre_lt).1]
  have hne : 1 + u ≠ 0 := fun h => by simp [h] at hre_pos
  have harg_pi : |(1 + u).arg| < Real.pi / 2 :=
    abs_arg_lt_pi_div_two_iff.mpr (.inl hre_pos)
  have hu_sq : u.re ^ 2 + u.im ^ 2 < Real.sin δ ^ 2 := by
    have h1 : ‖u‖ ^ 2 < Real.sin δ ^ 2 := sq_lt_sq' (by linarith [norm_nonneg u]) hu
    rwa [Complex.sq_norm, normSq_apply, ← sq, ← sq] at h1
  have h1u_sq : ‖1 + u‖ ^ 2 = (1 + u.re) ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm, normSq_apply]; simp [sq]
  have him_sq : u.im ^ 2 < ‖1 + u‖ ^ 2 * Real.sin δ ^ 2 := by
    rw [h1u_sq]
    by_cases hcos : Real.cos δ = 0
    · have hs1 : Real.sin δ ^ 2 = 1 := by
        nlinarith [Real.sin_sq_add_cos_sq δ]
      have hpos : 0 < (1 + u.re) ^ 2 := sq_pos_of_pos (by simpa using hre_pos)
      nlinarith
    · have hc_pos : 0 < Real.cos δ ^ 2 := sq_pos_of_ne_zero hcos
      nlinarith [mul_lt_mul_of_pos_right hu_sq hc_pos, Real.sin_sq_add_cos_sq δ,
        sq_nonneg (u.re + Real.sin δ ^ 2)]
  have hsin_arg_sq : (‖1 + u‖ * Real.sin |(1 + u).arg|) ^ 2 = u.im ^ 2 := by
    have hns := norm_mul_sin_arg (1 + u)
    simp only [add_im, one_im, zero_add] at hns
    rcases le_total 0 (1 + u).arg with ha | ha
    · rw [abs_of_nonneg ha, hns]
    · rw [abs_of_nonpos ha, Real.sin_neg, mul_neg, neg_sq, hns]
  have hn_pos : 0 < ‖1 + u‖ := norm_pos_iff.mpr hne
  have hsin_lt : Real.sin |(1 + u).arg| < Real.sin δ := by
    have hsq_lt : (Real.sin |(1 + u).arg|) ^ 2 < Real.sin δ ^ 2 := by
      nlinarith [sq_pos_of_pos hn_pos]
    have hnn : 0 ≤ Real.sin |(1 + u).arg| :=
      Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
    nlinarith [norm_nonneg u]
  by_contra! hge
  exact (Real.strictMonoOn_sin.le_iff_le
    ⟨by linarith [hδ₀, Real.pi_pos], hδ₁⟩
    ⟨by linarith [abs_nonneg (1 + u).arg, Real.pi_pos], harg_pi.le⟩).mpr hge |>.not_gt hsin_lt

/-- If `z ∈ Metric.ball c r` with `r ≤ ‖c‖ * sin δ` (`0 < δ ≤ π / 2`) and `[arg c - δ, arg c + δ]`
lies in `[-π, π]`, then `|arg z - arg c| < δ`. -/
theorem abs_arg_sub_lt_of_mem_ball {c z : ℂ} {r δ : ℝ} (hc : c ≠ 0)
    (hδ₀ : 0 < δ) (hδ₁ : δ ≤ Real.pi / 2)
    (hlo : -Real.pi ≤ c.arg - δ) (hhi : c.arg + δ ≤ Real.pi)
    (hr : r ≤ ‖c‖ * Real.sin δ) (hz : z ∈ Metric.ball c r) :
    |z.arg - c.arg| < δ := by
  set u : ℂ := (z - c) / c
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hu_lt : ‖u‖ < Real.sin δ := by
    rw [norm_div, div_lt_iff₀ hc_pos, mul_comm]
    exact (mem_ball_iff_norm.mp hz).trans_le hr
  have harg_u : |(1 + u).arg| < δ := abs_arg_one_add_lt_of_norm_lt_sin hδ₀ hδ₁ hu_lt
  have h1u_ne : 1 + u ≠ 0 := by
    intro h0
    have : ‖u‖ = 1 := by
      have hu_eq : u = -1 := eq_neg_of_add_eq_zero_right h0
      simp [hu_eq]
    linarith [Real.sin_le_one δ]
  have hz_eq : z = c * (1 + u) := by
    dsimp [u]
    field_simp
    ring
  have hIoc : c.arg + (1 + u).arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    obtain ⟨h1, h2⟩ := abs_lt.mp harg_u
    exact ⟨by linarith, by linarith⟩
  rw [hz_eq, arg_mul hc h1u_ne hIoc]
  simpa using harg_u

/-- **Sector containment for an open disc.** If `c ≠ 0`, `θ₁` and `θ₂` lie in `[-π, π]`, and
`0 < δ ≤ min (π / 2) (min (arg c - θ₁) (θ₂ - arg c))` with `r ≤ ‖c‖ * sin δ`, then every
`z ∈ Metric.ball c r` satisfies `θ₁ < arg z ∧ arg z < θ₂`. -/
theorem arg_mem_Ioo_of_mem_ball {θ₁ θ₂ : ℝ} {c z : ℂ} {r δ : ℝ}
    (hθ₁ : -Real.pi ≤ θ₁) (hθ₂ : θ₂ ≤ Real.pi) (hc : c ≠ 0)
    (hδ₀ : 0 < δ) (hδ₁ : δ ≤ Real.pi / 2)
    (hd₁ : δ ≤ c.arg - θ₁) (hd₂ : δ ≤ θ₂ - c.arg)
    (hr : r ≤ ‖c‖ * Real.sin δ) (hz : z ∈ Metric.ball c r) :
    θ₁ < z.arg ∧ z.arg < θ₂ := by
  have h := abs_lt.mp <| abs_arg_sub_lt_of_mem_ball hc hδ₀ hδ₁
    (by linarith) (by linarith) hr hz
  exact ⟨by linarith, by linarith⟩

end Complex
