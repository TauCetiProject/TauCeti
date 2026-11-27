/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Norm and argument bounds in complex sectors

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
`(1 - max c (-1)) / 2 * (t + ‖z‖) ≤ ‖t - z‖`, and in multiplicative form
`(1 - max c (-1)) / 2 * (1 + ‖z‖ t) ≤ ‖1 - z t‖` (`Complex.mul_one_add_le_norm_one_sub_mul`).
These inequalities control reciprocal kernels in sectorial and Stieltjes integrals and resolvent
symbols. A nonzero point of such a sector, with `0 < δ`, lies in the slit plane, as does every
point of an exterior sector `{z : ℂ | r < ‖z‖ ∧ |arg z| < θ}` with `0 ≤ r` and `θ ≤ π`
(`Complex.setOf_lt_norm_and_abs_arg_lt_subset_inter_slitPlane`), and every
sector `{z : ℂ | |arg z| < α ∧ r < ‖z‖}` is preconnected
(`Complex.isPreconnected_setOf_abs_arg_lt_and_lt_norm`).

For open discs centered in a sector, the tangent angle from the origin to `Metric.ball c r` is
controlled by `r / ‖c‖`: when `0 ≤ δ ≤ π / 2` and `r ≤ ‖c‖ * sin δ` (with `arg c ± δ` avoiding the
branch cut), every `z ∈ Metric.ball c r` satisfies `|arg z - arg c| < δ`
(`Complex.abs_arg_sub_arg_lt_of_mem_ball`), placing the whole disc inside an open sector
(`Complex.arg_mem_Ioo_of_mem_ball`).

Discs whose radii are a fixed multiple `c ≤ 1 / 2` of the norm of their centers, centered at
the points of a closed sector `|arg z| ≤ θ'`, stay inside every larger open sector `|arg w| < θ`,
by compactness of the arc of unit directions of the closed sector, and on such discs the norms
are comparable to the norm of the center (`TauCeti.exists_pos_forall_mem_closedBall_abs_arg_lt`;
the disc at the vertex is the vertex itself). Discs centered at points with `2 A < ‖z‖` also lie
in `{A < ‖w‖}`, hence in the truncated sector `{A < ‖w‖, |arg w| < θ}`
(`TauCeti.closedBall_subset_setOf_lt_norm_and_abs_arg_lt`). The disc statements and proofs are
adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMFMathlib/Analysis/Complex/Sector.lean`, where
the sectors may have any bisector.
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

/-- On the sector `Re r ≤ c ‖r‖`, the numbers `1 - r t` with a nonnegative real `t` satisfy
`(1 - max c (-1)) / 2 * (1 + ‖r‖ t) ≤ ‖1 - r t‖`, which keeps them away from `0` for `c < 1`. -/
theorem mul_one_add_le_norm_one_sub_mul {c : ℝ} {r : ℂ} (hr : r.re ≤ c * ‖r‖) {t : ℝ}
    (ht : 0 ≤ t) : (1 - max c (-1)) / 2 * (1 + ‖r‖ * t) ≤ ‖1 - r * t‖ := by
  have hnorm : ‖r * t‖ = ‖r‖ * t := by rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht]
  have h := mul_add_norm_le_norm_ofReal_sub (z := r * t) zero_le_one (by
    rw [hnorm]
    simpa [mul_assoc] using mul_le_mul_of_nonneg_right hr ht)
  rwa [hnorm, Complex.ofReal_one] at h

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

/-- For `0 ≤ r` and `θ ≤ π`, the open exterior sector `{z : ℂ | r < ‖z‖ ∧ |arg z| < θ}` lies in
the slit exterior `{z | r < ‖z‖} ∩ slitPlane`. -/
theorem setOf_lt_norm_and_abs_arg_lt_subset_inter_slitPlane {r θ : ℝ} (hr : 0 ≤ r)
    (hθ : θ ≤ Real.pi) : {z : ℂ | r < ‖z‖ ∧ |z.arg| < θ} ⊆ {z | r < ‖z‖} ∩ slitPlane :=
  fun _ hz ↦ ⟨hz.1, mem_slitPlane_of_abs_arg_lt (hz.2.trans_le hθ)
    (norm_pos_iff.1 (hr.trans_lt hz.1))⟩

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

/-- **Sharp tangent-angle bound on `ball 1 (sin δ)`.** If `0 ≤ δ ≤ π / 2` and `‖u‖ < sin δ`, then
`|(1 + u).arg| < δ`. -/
theorem abs_arg_one_add_lt_of_norm_lt_sin {u : ℂ} {δ : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ Real.pi / 2) (hu : ‖u‖ < Real.sin δ) :
    |(1 + u).arg| < δ := by
  have hre_lt : |u.re| < 1 :=
    (abs_re_le_norm u).trans_lt (hu.trans_le (Real.sin_le_one δ))
  have hre_pos : 0 < (1 + u).re := by simp; linarith [(abs_lt.mp hre_lt).1]
  have harg_pi : |(1 + u).arg| < Real.pi / 2 :=
    abs_arg_lt_pi_div_two_iff.mpr (.inl hre_pos)
  have hu_sq : Real.sin (1 + u).arg ^ 2 ≤ ‖u‖ ^ 2 := by
    have h1 := norm_circleMap_sub_circleMap_sq 0 ‖1 + u‖ 1 (1 + u).arg 0
    have hcm : circleMap 0 1 0 = 1 := by simp [circleMap_zero]
    rw [circleMap_zero_norm_arg, hcm, add_sub_cancel_left, one_pow, mul_one, sub_zero] at h1
    have hcs := Real.sin_sq_add_cos_sq (1 + u).arg
    nlinarith [sq_nonneg (‖1 + u‖ - Real.cos (1 + u).arg)]
  have hsin_lt : Real.sin |(1 + u).arg| < Real.sin δ := by
    have hsq : Real.sin |(1 + u).arg| ^ 2 < Real.sin δ ^ 2 := by
      rw [← sq_abs (Real.sin (1 + u).arg),
        Real.abs_sin_eq_sin_abs_of_abs_le_pi (abs_arg_le_pi _)] at hu_sq
      exact hu_sq.trans_lt (sq_lt_sq' (by linarith [norm_nonneg u]) hu)
    have hnn₁ : 0 ≤ Real.sin |(1 + u).arg| :=
      Real.sin_nonneg_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos])
    have hnn₂ : 0 ≤ Real.sin δ := Real.sin_nonneg_of_nonneg_of_le_pi hδ₀ (by linarith [Real.pi_pos])
    nlinarith
  by_contra! hge
  exact (Real.strictMonoOn_sin.le_iff_le
    ⟨by linarith [hδ₀, Real.pi_pos], hδ₁⟩
    ⟨by linarith [abs_nonneg (1 + u).arg, Real.pi_pos], harg_pi.le⟩).mpr hge |>.not_gt hsin_lt

/-- If `z ∈ Metric.ball c r` with `r ≤ ‖c‖ * sin δ` (`0 ≤ δ ≤ π / 2`) and `[arg c - δ, arg c + δ]`
lies in `[-π, π]`, then `|arg z - arg c| < δ`. -/
theorem abs_arg_sub_arg_lt_of_mem_ball {c z : ℂ} {r δ : ℝ}
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ Real.pi / 2)
    (hlo : -Real.pi ≤ c.arg - δ) (hhi : c.arg + δ ≤ Real.pi)
    (hr : r ≤ ‖c‖ * Real.sin δ) (hz : z ∈ Metric.ball c r) :
    |z.arg - c.arg| < δ := by
  have hz_lt : ‖z - c‖ < r := mem_ball_iff_norm.mp hz
  have hc : c ≠ 0 := fun h0 => by
    rw [h0, norm_zero, zero_mul] at hr
    linarith [norm_nonneg (z - c)]
  set u : ℂ := (z - c) / c
  have hc_pos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hu_lt : ‖u‖ < Real.sin δ := by
    rw [norm_div, div_lt_iff₀ hc_pos, mul_comm]
    exact hz_lt.trans_le hr
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

/-- **Sector containment for an open disc.** If `θ₁` and `θ₂` lie in `[-π, π]`, and
`0 ≤ δ ≤ min (π / 2) (min (arg c - θ₁) (θ₂ - arg c))` with `r ≤ ‖c‖ * sin δ`, then every
`z ∈ Metric.ball c r` satisfies `z.arg ∈ Set.Ioo θ₁ θ₂`. -/
theorem arg_mem_Ioo_of_mem_ball {θ₁ θ₂ : ℝ} {c z : ℂ} {r δ : ℝ}
    (hθ₁ : -Real.pi ≤ θ₁) (hθ₂ : θ₂ ≤ Real.pi)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ Real.pi / 2)
    (hd₁ : δ ≤ c.arg - θ₁) (hd₂ : δ ≤ θ₂ - c.arg)
    (hr : r ≤ ‖c‖ * Real.sin δ) (hz : z ∈ Metric.ball c r) :
    z.arg ∈ Set.Ioo θ₁ θ₂ := by
  have h := abs_lt.mp <| abs_arg_sub_arg_lt_of_mem_ball hδ₀ hδ₁
    (by linarith) (by linarith) hr hz
  exact ⟨by linarith, by linarith⟩

end Complex

namespace TauCeti

open Complex Metric Set

/-- For `θ' < θ ≤ π`, the closed balls of radius `c ‖z‖` around the points `z` of the closed
sector `|arg z| ≤ θ'` stay in the open sector `|arg w| < θ`, for some `0 < c ≤ 1 / 2`. -/
private theorem exists_pos_forall_mem_closedBall_abs_arg_lt_of_le_pi {θ θ' : ℝ} (hθ : θ ≤ π)
    (hθ' : θ' < θ) : ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ, |z.arg| ≤ θ' →
      ∀ w ∈ closedBall z (c * ‖z‖), |w.arg| < θ := by
  let K : Set ℂ := (fun φ : ℝ => exp (φ * I)) '' Icc (-θ') θ'
  let U : Set ℂ := slitPlane ∩ (fun z : ℂ => |z.arg|) ⁻¹' Iio θ
  have hK : IsCompact K := isCompact_Icc.image (by fun_prop)
  have hU : IsOpen U := continuousOn_arg.abs.isOpen_inter_preimage isOpen_slitPlane isOpen_Iio
  have hKU : K ⊆ U := by
    rintro _ ⟨φ, hφ, rfl⟩
    have ha : (exp (φ * I)).arg = φ := by
      rw [arg_exp_mul_I, toIocMod_eq_self]
      constructor <;> linarith [hφ.1, hφ.2]
    refine ⟨mem_slitPlane_iff_arg.mpr ⟨by linarith [hφ.2], exp_ne_zero _⟩, ?_⟩
    rw [Set.mem_preimage, ha, Set.mem_Iio, abs_lt]
    constructor <;> linarith [hφ.1, hφ.2]
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), min_le_right _ _, fun z harg w hw => ?_⟩
  rcases eq_or_ne z 0 with rfl | hz
  · rw [norm_zero, mul_zero, closedBall_zero, mem_singleton_iff] at hw
    rw [hw]
    exact harg.trans_lt hθ'
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hzr : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hz0.ne'
  rw [mem_closedBall, dist_eq_norm] at hw
  have hunit : z / (‖z‖ : ℂ) ∈ K := by
    refine ⟨z.arg, abs_le.mp harg, ?_⟩
    rw [eq_div_iff hzr, mul_comm, norm_mul_exp_arg_mul_I]
  have hdist : dist (w / (‖z‖ : ℂ)) (z / (‖z‖ : ℂ)) ≤ δ := by
    rw [dist_eq_norm, ← sub_div, norm_div, norm_real, Real.norm_of_nonneg hz0.le]
    exact ((div_le_iff₀ hz0).mpr hw).trans (min_le_left _ _)
  have hwU := (hδU (mem_cthickening_of_dist_le _ _ _ K hunit hdist)).2
  rwa [Set.mem_preimage, Set.mem_Iio, arg_div_ofReal w hz0] at hwU

/-- For `θ' < θ` there is `0 < c ≤ 1 / 2` such that the closed balls of radius `c ‖z‖` around
the points `z` of the closed sector `|arg z| ≤ θ'` stay in the open sector `|arg w| < θ`, and the
norms in these balls lie between `‖z‖ / 2` and `2 ‖z‖`. -/
theorem exists_pos_forall_mem_closedBall_abs_arg_lt {θ θ' : ℝ} (hθ' : θ' < θ) :
    ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ, |z.arg| ≤ θ' → ∀ w ∈ closedBall z (c * ‖z‖),
      |w.arg| < θ ∧ ‖z‖ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * ‖z‖ := by
  obtain ⟨c, hc, hc2, h⟩ : ∃ c > 0, c ≤ 1 / 2 ∧ ∀ z : ℂ, |z.arg| ≤ θ' →
      ∀ w ∈ closedBall z (c * ‖z‖), |w.arg| < θ := by
    rcases le_or_gt θ π with hθ | hθ
    · exact exists_pos_forall_mem_closedBall_abs_arg_lt_of_le_pi hθ hθ'
    · exact ⟨1 / 2, by norm_num, le_rfl, fun _ _ w _ => (abs_arg_le_pi w).trans_lt hθ⟩
  refine ⟨c, hc, hc2, fun z harg w hw => ⟨h z harg w hw, ?_⟩⟩
  rw [mem_closedBall, dist_eq_norm] at hw
  have hnear : ‖w - z‖ ≤ ‖z‖ / 2 := hw.trans (by nlinarith [norm_nonneg z])
  have h1 := norm_le_norm_add_norm_sub z w
  have h2 := norm_le_norm_add_norm_sub w z
  rw [norm_sub_rev] at h1
  constructor <;> linarith

/-- If `c ≤ 1 / 2`, the closed ball of radius `c ‖z‖` around `z` lies in the open sector
`|arg w| < θ`, and `2 A < ‖z‖`, then the ball lies in the truncated sector
`{A < ‖w‖, |arg w| < θ}`: its points have norm at least `‖z‖ / 2`. -/
theorem closedBall_subset_setOf_lt_norm_and_abs_arg_lt {θ A c : ℝ} {z : ℂ} (hc : c ≤ 1 / 2)
    (hball : ∀ w ∈ closedBall z (c * ‖z‖), |w.arg| < θ) (hz : 2 * A < ‖z‖) :
    closedBall z (c * ‖z‖) ⊆ {w | A < ‖w‖ ∧ |w.arg| < θ} := fun w hw => by
  refine ⟨?_, hball w hw⟩
  rw [mem_closedBall, dist_eq_norm, norm_sub_rev] at hw
  have h := norm_sub_norm_le z w
  have hcz := mul_le_mul_of_nonneg_right hc (norm_nonneg z)
  linarith

end TauCeti
