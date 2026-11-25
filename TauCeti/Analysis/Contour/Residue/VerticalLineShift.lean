/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import TauCeti.Analysis.Contour.Residue.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import TauCeti.Analysis.Contour.Residue.Rectangle
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Shifting a vertical line of integration past poles

Let `F` be continuous on the closed strip `d ≤ Re t ≤ c` except at a finite set `P` of poles
inside the open strip, complex differentiable on the open strip `d < Re t < c` off `P`, integrable
on both boundary lines, and such that the horizontal connectors `∫_d^c F(x + iT) dx` tend to `0`
as `T → ±∞`. Then

`∫_ℝ F(c + iy) dy - ∫_ℝ F(d + iy) dy = 2π ∑_{p ∈ P} Res(F, p)`.

This is the line shift behind DLMF 2.5.6–2.5.7 and behind the evaluation of Mellin–Barnes
integrals by residues. The proof applies Tau Ceti's rectangle residue theorem
`TauCeti.Contour.rectangle_boundary_integral_eq_residues` to `[d, c] × [-T, T]`, which winds once
around every pole, and lets `T → ∞`. The line integrals use `dy`, so the factor `i` of `dt = i dy`
cancels against the `2πi` of the residue theorem. The horizontal connectors vanish when the
integrand decays uniformly on the strip (`TauCeti.Contour.tendsto_intervalIntegral_horizontal`).

## Main results

* `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue`: the line shift past
  meromorphic singularities of any order,
  `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_residue_of_norm_le`: its norm-bound
  corollary, and `TauCeti.Contour.tendsto_intervalIntegral_vertical_sub`: its symmetric-limit form,
  which needs no integrability on the two lines.
* `TauCeti.Contour.integral_vertical_sub_eq_two_pi_mul_sum_range_residue`: its iteration across
  finitely many lines with one singularity between consecutive lines, and
  `TauCeti.Contour.tendsto_sum_range_residue`, `TauCeti.Contour.hasSum_residue`: the resulting
  residue series.

The statements follow the lean-DLMF project (<https://github.com/bjbraams/lean-DLMF>), files
`DLMFMathlib/Analysis/Complex/VerticalResidues.lean` and
`DLMF/AsymptoticApproximations/Mellin/Transforms.lean`. The line shift is proved here through Tau
Ceti's rectangle residue theorem instead of lean-DLMF's own contour machinery.
-/

public section

open Complex Set Filter MeasureTheory
open scoped Topology Real Interval

namespace TauCeti.Contour

/-- **The symmetric line shift.** Let `F` be continuous on the closed strip `d ≤ Re t ≤ c` except
at a finite set `P` of points of the open strip, complex differentiable on the open strip
`d < Re t < c` off `P`, meromorphic at each point of `P`, and with horizontal connectors
`∫_d^c F(x + iT) dx` tending to `0` as `T → ±∞`. Then
`∫_{-T}^{T} F(c + iy) dy - ∫_{-T}^{T} F(d + iy) dy → 2π ∑_{p ∈ P} Res(F, p)` as `T → ∞`; no
integrability on the two lines is needed. -/
theorem tendsto_intervalIntegral_vertical_sub (F : ℂ → ℂ) {c d : ℝ} (hdc : d ≤ c)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hFc : ContinuousOn F ({t : ℂ | d ≤ t.re ∧ t.re ≤ c} \ (P : Set ℂ)))
    (hFd : DifferentiableOn ℂ F ({t : ℂ | d < t.re ∧ t.re < c} \ (P : Set ℂ)))
    (hmero : ∀ p ∈ P, MeromorphicAt F p)
    (htop : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atBot (𝓝 0)) :
    Tendsto (fun T : ℝ =>
        (∫ y : ℝ in (-T)..T, F (c + y * I)) - ∫ y : ℝ in (-T)..T, F (d + y * I))
      atTop (𝓝 (2 * π * ∑ p ∈ P, residue F p)) := by
  have hev : ∀ᶠ T : ℝ in atTop, 0 < T ∧ ∀ p ∈ P, |p.im| < T :=
    (eventually_gt_atTop 0).and ((Finset.eventually_all P).mpr fun p _ => eventually_gt_atTop _)
  -- Solve the rectangle identity for the difference of the vertical edges.
  have hlim : Tendsto (fun T : ℝ => 2 * π * ∑ p ∈ P, residue F p - I⁻¹ *
      ((∫ x : ℝ in d..c, F (x + ((-T : ℝ) : ℂ) * I)) - ∫ x : ℝ in d..c, F (x + T * I)))
      atTop (𝓝 (2 * π * ∑ p ∈ P, residue F p - I⁻¹ * (0 - 0))) :=
    tendsto_const_nhds.sub (((hbot.comp tendsto_neg_atTop_atBot).sub htop).const_mul _)
  rw [sub_zero, mul_zero, sub_zero] at hlim
  refine hlim.congr' (hev.mono fun T hT => ?_)
  have h := rectangle_boundary_integral_eq_residues hdc (by linarith [hT.1] : -T ≤ T)
    (fun p hp => ⟨hP p hp, abs_lt.mp (hT.2 p hp)⟩)
    (hFc.mono (sdiff_subset_sdiff_left fun _ hz => hz.1))
    (hFd.mono (sdiff_subset_sdiff_left fun _ hz => hz.1)) hmero
  linear_combination (-I⁻¹) * h + ((∫ y : ℝ in (-T)..T, F (c + y * I)) -
    (∫ y : ℝ in (-T)..T, F (d + y * I)) - 2 * π * ∑ p ∈ P, residue F p) *
      inv_mul_cancel₀ I_ne_zero

/-- **Shifting the line of integration past meromorphic singularities.** Let `F` be continuous on
the closed strip `d ≤ Re t ≤ c` except at a finite set `P` of points of the open strip, complex
differentiable on the open strip `d < Re t < c` off `P`, meromorphic at each point of `P`,
integrable on the lines `Re t = c` and `Re t = d`, and with horizontal connectors
`∫_d^c F(x + iT) dx` tending to `0` as `T → ±∞`. Then
`∫_ℝ F(c + iy) dy - ∫_ℝ F(d + iy) dy = 2π ∑_{p ∈ P} Res(F, p)`. The poles may have any order;
a simple pole `F(t) = g(t)/(t - p)` with `g` analytic at `p` is meromorphic by
`MeromorphicAt.meromorphicAt_congr`. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_residue (F : ℂ → ℂ) {c d : ℝ} (hdc : d ≤ c)
    (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hFc : ContinuousOn F ({t : ℂ | d ≤ t.re ∧ t.re ≤ c} \ (P : Set ℂ)))
    (hFd : DifferentiableOn ℂ F ({t : ℂ | d < t.re ∧ t.re < c} \ (P : Set ℂ)))
    (hmero : ∀ p ∈ P, MeromorphicAt F p)
    (hc : Integrable fun y : ℝ => F (c + y * I)) (hd : Integrable fun y : ℝ => F (d + y * I))
    (htop : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atBot (𝓝 0)) :
    (∫ y : ℝ, F (c + y * I)) - ∫ y : ℝ, F (d + y * I) =
      2 * π * ∑ p ∈ P, residue F p :=
  tendsto_nhds_unique
    ((intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id).sub
      (intervalIntegral_tendsto_integral hd tendsto_neg_atTop_atBot tendsto_id))
    (tendsto_intervalIntegral_vertical_sub F hdc P hP hFc hFd hmero htop hbot)

/-- **Shifting a vertical-line integral under uniform horizontal decay.** If on horizontal
segments `[d, c] ± i T` the integrand is eventually bounded by `B T` with `B T → 0` as `T → +∞`,
the horizontal connectors vanish in the limit and
`integral_vertical_sub_eq_two_pi_mul_sum_residue` applies. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_residue_of_norm_le (F : ℂ → ℂ) {c d : ℝ}
    (hdc : d ≤ c) (P : Finset ℂ) (hP : ∀ p ∈ P, d < p.re ∧ p.re < c)
    (hFc : ContinuousOn F ({t : ℂ | d ≤ t.re ∧ t.re ≤ c} \ (P : Set ℂ)))
    (hFd : DifferentiableOn ℂ F ({t : ℂ | d < t.re ∧ t.re < c} \ (P : Set ℂ)))
    (hmero : ∀ p ∈ P, MeromorphicAt F p)
    (hc : Integrable fun y : ℝ => F (c + y * I)) (hd : Integrable fun y : ℝ => F (d + y * I))
    {B : ℝ → ℝ} (hB : Tendsto B atTop (𝓝 0))
    (hbound : ∀ᶠ (T : ℝ) in atTop, ∀ x ∈ Icc d c,
      ‖F ((x : ℂ) + T * I)‖ ≤ B T ∧ ‖F ((x : ℂ) - T * I)‖ ≤ B T) :
    (∫ y : ℝ, F (c + y * I)) - ∫ y : ℝ, F (d + y * I) =
      2 * π * ∑ p ∈ P, residue F p := by
  have hseg (g : ℝ → ℝ → ℂ)
      (hg : ∀ᶠ (T : ℝ) in atTop, ∀ x ∈ Icc d c, ‖g T x‖ ≤ B T) :
      Tendsto (fun T : ℝ => ∫ x : ℝ in d..c, g T x) atTop (𝓝 0) :=
    TauCeti.intervalIntegral.tendsto_integral_nhds_zero_of_ae_norm_le hB <|
      hg.mono fun T hTB => Eventually.of_forall fun x hx =>
        hTB x (Ioc_subset_Icc_self (by rwa [uIoc_of_le hdc] at hx))
  have htop : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atTop (𝓝 0) :=
    hseg (fun T x => F ((x : ℂ) + T * I)) (hbound.mono fun T hT x hx => (hT x hx).1)
  have hbot_neg : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + (-T : ℝ) * I)) atTop (𝓝 0) := by
    simpa only [ofReal_neg, neg_mul, ← sub_eq_add_neg] using
      hseg (fun T x => F ((x : ℂ) - T * I)) (hbound.mono fun T hT x hx => (hT x hx).2)
  have hbot : Tendsto (fun T : ℝ => ∫ x in d..c, F (x + T * I)) atBot (𝓝 0) := by
    simpa only [Function.comp_def, neg_neg] using hbot_neg.comp tendsto_neg_atBot_atTop
  exact integral_vertical_sub_eq_two_pi_mul_sum_residue F hdc P hP hFc hFd hmero hc hd htop hbot

/-- **Iterated line shifts.** Let `c₀, c₁, …, c_N` be lines with exactly one singularity `p n` of
`F`, at which `F` is meromorphic, in each strip `c (n + 1) < Re t < c n` for `n < N`, each strip
satisfying the hypotheses of `integral_vertical_sub_eq_two_pi_mul_sum_residue`.
The poles may have any order. Then
`∫_ℝ F(c₀ + iy) dy - ∫_ℝ F(c_N + iy) dy = 2π ∑_{n < N} Res(F, p n)`. -/
theorem integral_vertical_sub_eq_two_pi_mul_sum_range_residue (F : ℂ → ℂ) {c : ℕ → ℝ}
    {p : ℕ → ℂ} (N : ℕ)
    (hp : ∀ n < N, c (n + 1) < (p n).re ∧ (p n).re < c n)
    (hFc : ∀ n < N, ContinuousOn F ({t : ℂ | c (n + 1) ≤ t.re ∧ t.re ≤ c n} \ {p n}))
    (hFd : ∀ n < N, DifferentiableOn ℂ F ({t : ℂ | c (n + 1) < t.re ∧ t.re < c n} \ {p n}))
    (hmero : ∀ n < N, MeromorphicAt F (p n))
    (hint : ∀ n ≤ N, Integrable fun y : ℝ => F (c n + y * I))
    (htop : ∀ n < N,
      Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atTop (𝓝 0))
    (hbot : ∀ n < N,
      Tendsto (fun T : ℝ => ∫ x in c (n + 1)..c n, F (x + T * I)) atBot (𝓝 0)) :
    (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * π * ∑ n ∈ Finset.range N, residue F (p n) := by
  have hstep : ∀ n ∈ Finset.range N, (∫ y : ℝ, F (c n + y * I)) -
      ∫ y : ℝ, F (c (n + 1) + y * I) = 2 * π * residue F (p n) := fun n hn => by
    have hn := Finset.mem_range.mp hn
    have h := integral_vertical_sub_eq_two_pi_mul_sum_residue F
      ((hp n hn).1.trans (hp n hn).2).le {p n} (by simpa using hp n hn)
      (by simpa using hFc n hn) (by simpa using hFd n hn) (by simpa using hmero n hn)
      (hint n hn.le) (hint (n + 1) hn) (htop n hn) (hbot n hn)
    simpa using h
  rw [← Finset.sum_range_sub' (fun n => ∫ y : ℝ, F (c n + y * I)) N, Finset.mul_sum]
  exact Finset.sum_congr rfl hstep

/-- If the partial residue sums of iterated line shifts satisfy the identity of
`integral_vertical_sub_eq_two_pi_mul_sum_range_residue` and the integrals on the lines `c N`
tend to `0`, the partial residue sums tend to `(2π)⁻¹ ∫_ℝ F(c₀ + iy) dy`. -/
theorem tendsto_sum_range_residue {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    (hsum : ∀ N, (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * π * ∑ n ∈ Finset.range N, residue F (p n))
    (hlim : Tendsto (fun N => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0)) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, residue F (p n)) atTop
      (𝓝 ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, F (c 0 + y * I))) := by
  have h2π : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  have h := ((tendsto_const_nhds (x := ∫ y : ℝ, F (c 0 + y * I))).sub hlim).const_mul
    (2 * π : ℂ)⁻¹
  rw [sub_zero] at h
  refine h.congr fun N => ?_
  rw [hsum N, ← mul_assoc, inv_mul_cancel₀ h2π, one_mul]

/-- Under the hypotheses of `tendsto_sum_range_residue` (the identity of
`integral_vertical_sub_eq_two_pi_mul_sum_range_residue` for every `N`, and
`∫_ℝ F(c_N + iy) dy → 0`), if the residue series is summable then its sum is
`(2π)⁻¹ ∫_ℝ F(c₀ + iy) dy`. -/
theorem hasSum_residue {F : ℂ → ℂ} {c : ℕ → ℝ} {p : ℕ → ℂ}
    (hsum : ∀ N, (∫ y : ℝ, F (c 0 + y * I)) - ∫ y : ℝ, F (c N + y * I) =
      2 * π * ∑ n ∈ Finset.range N, residue F (p n))
    (hlim : Tendsto (fun N => ∫ y : ℝ, F (c N + y * I)) atTop (𝓝 0))
    (hs : Summable fun n => residue F (p n)) :
    HasSum (fun n => residue F (p n)) ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, F (c 0 + y * I)) :=
  (hs.hasSum_iff_tendsto_nat).mpr (tendsto_sum_range_residue hsum hlim)

end TauCeti.Contour
