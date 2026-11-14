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
`c * (‖s‖ + t) ≤ ‖s + t‖`, where `0 ≤ c ≤ 1` depends only on the angular separation. More
sharply, `cos (arg z / 2) * (‖z‖ + t) ≤ ‖z + t‖` for every `z : ℂ` and `t : ℝ`, and on the
closed sector `|arg z| ≤ π - δ` with `0 ≤ δ` one has `sin (δ / 2) * (‖z‖ + t) ≤ ‖z + t‖`
(as well as `c = (1 - cos δ) / 2` for `t ≥ 0`). These inequalities control reciprocal kernels in
sectorial and Stieltjes integrals. A nonzero point of such a sector, with `0 < δ`, lies in the
slit plane, and every open sector `{z : ℂ | |arg z| < α ∧ r < ‖z‖}` is preconnected
(`Complex.isPreconnected_setOf_abs_arg_lt_and_lt_norm`).
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

/-- Every open sector `{z : ℂ | |arg z| < α ∧ r < ‖z‖}` is preconnected. -/
theorem isPreconnected_setOf_abs_arg_lt_and_lt_norm {α r : ℝ} :
    IsPreconnected {z : ℂ | |z.arg| < α ∧ r < ‖z‖} := by
  let φ : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * Complex.exp ((p.2 : ℂ) * Complex.I)
  have hφ : Continuous φ := by fun_prop
  let R : Set ℝ := if r < 0 then Set.Ici 0 else Set.Ioi r
  let T : Set ℝ := if Real.pi < α then Set.univ else Set.Ioo (-α) α
  have hR : IsPreconnected R := by
    dsimp only [R]
    split_ifs <;> [exact isPreconnected_Ici; exact isPreconnected_Ioi]
  have hT : IsPreconnected T := by
    dsimp only [T]
    split_ifs <;> [exact isPreconnected_univ; exact isPreconnected_Ioo]
  have himg : φ '' (R ×ˢ T) = {z : ℂ | |z.arg| < α ∧ r < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨ρ, θ⟩, ⟨hρ, hθ⟩, rfl⟩
      have hρ0 : 0 ≤ ρ := by
        dsimp only [R] at hρ
        split_ifs at hρ with hr
        · exact hρ
        · exact (not_lt.mp hr).trans hρ.le
      have hnorm : ‖φ (ρ, θ)‖ = ρ := by
        dsimp only [φ]
        rw [norm_mul, norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_of_nonneg hρ0, mul_one]
      have hrρ : r < ρ := by
        dsimp only [R] at hρ
        split_ifs at hρ with hr
        · exact hr.trans_le hρ
        · exact hρ
      refine ⟨?_, by rwa [hnorm]⟩
      dsimp only [T] at hθ
      split_ifs at hθ with hα
      · exact (abs_arg_le_pi _).trans_lt hα
      · rcases hρ0.eq_or_lt with rfl | hρ_pos
        · dsimp only [φ]
          rw [ofReal_zero, zero_mul, arg_zero, abs_zero]
          linarith [hθ.1, hθ.2]
        · have harg : (φ (ρ, θ)).arg = θ := by
            dsimp only [φ]
            rw [arg_real_mul _ hρ_pos, arg_exp_mul_I, toIocMod_eq_self]
            exact ⟨by linarith [hθ.1, not_lt.mp hα], by linarith [hθ.2, not_lt.mp hα]⟩
          rw [harg]
          exact abs_lt.mpr hθ
    · rintro ⟨harg, hnorm⟩
      refine ⟨(‖z‖, z.arg), ⟨?_, ?_⟩, norm_mul_exp_arg_mul_I z⟩
      · dsimp only [R]
        split_ifs with hr
        · exact norm_nonneg z
        · exact hnorm
      · dsimp only [T]
        split_ifs with hα
        · exact Set.mem_univ _
        · exact abs_lt.mp harg
  rw [← himg]
  exact (hR.prod hT).image φ hφ.continuousOn

end Complex
