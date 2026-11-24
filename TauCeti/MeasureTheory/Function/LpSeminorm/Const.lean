/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A constant bounded almost everywhere by a function in `Lᵖ`

Throughout this file, let `p ≠ 0`. If a real number `t` satisfies `t ≤ ‖u y‖` for almost every `y`
with respect to a nonzero measure `μ` and `u` has finite `Lᵖ(μ)` seminorm, then taking `Lᵖ(μ)`
seminorms of both sides gives `t ≤ μ(X)^{-1/p} ‖u‖_{Lᵖ(μ)}`
(`MeasureTheory.le_toReal_eLpNorm_div_of_ae_le`).

Applied to `‖c‖ - A`, this is the averaging step that turns an almost-everywhere oscillation bound
`dist c (u y) ≤ A` with respect to a nonzero measure `μ` into a bound on `‖c‖`: if `u` has finite
`Lᵖ(μ)` seminorm, then `‖c‖ ≤ A + ‖u‖_{Lᵖ(μ)} / μ(X)^{1/p}`
(`MeasureTheory.norm_le_add_toReal_eLpNorm_div_of_ae_dist_le`).

For a planar disc `B(x, r) ⊆ ℂ` of radius `r > 0`, whose area `π r²` is at least `r²`, if `u` has
finite `Lᵖ(B(x, r))` seminorm and `t ≤ ‖u y‖` almost everywhere on `B(x, r)`, then
`t ≤ r^{-2/p} ‖u‖_{Lᵖ(B(x, r))}` (`Complex.le_rpow_neg_mul_toReal_eLpNorm_restrict_ball_of_ae_le`).
-/

public section

open Metric
open scoped ENNReal NNReal

namespace MeasureTheory

variable {X F : Type*} [MeasurableSpace X] {μ : Measure X} [SeminormedAddCommGroup F] {p : ℝ≥0∞}

/-- **A constant bounded by `‖u‖` almost everywhere.** Let `p ≠ 0`, let `μ` be a nonzero
measure and let `u` have finite `Lᵖ(μ)` seminorm. If `t ≤ ‖u y‖` for almost every `y`, then
`t ≤ ‖u‖_{Lᵖ(μ)} / μ(X)^{1/p}`. -/
theorem le_toReal_eLpNorm_div_of_ae_le (hp : p ≠ 0) (h0 : μ ≠ 0)
    {u : X → F} (hu : eLpNorm u p μ ≠ ∞) {t : ℝ} (h : ∀ᵐ y ∂μ, t ≤ ‖u y‖) :
    t ≤ (eLpNorm u p μ).toReal / (μ Set.univ).toReal ^ (1 / p.toReal) := by
  rcases le_or_gt t 0 with ht | ht
  · exact ht.trans (by positivity)
  have hle : eLpNorm (fun _ : X => t) p μ ≤ eLpNorm u p μ :=
    eLpNorm_mono_eNorm_ae aestronglyMeasurable_const
      (h.mono fun y hy => by
        rw [eNorm_le_iff_norm_le, Real.norm_of_nonneg ht.le]
        exact hy)
  rw [eLpNorm_const _ hp h0] at hle
  have hpow : μ Set.univ ^ (1 / p.toReal) ≠ ∞ := fun htop => by
    rw [htop, ENNReal.mul_top (eNorm_ne_zero.2 ht.ne')] at hle
    exact hu (top_le_iff.1 hle)
  have hpos : 0 < (μ Set.univ ^ (1 / p.toReal)).toReal :=
    ENNReal.toReal_pos
      (ENNReal.rpow_pos_of_nonneg (Measure.measure_univ_pos.2 h0) (by positivity)).ne' hpow
  have hreal := ENNReal.toReal_mono hu hle
  rw [ENNReal.toReal_mul, toReal_eNorm, Real.norm_of_nonneg ht.le] at hreal
  rw [ENNReal.toReal_rpow, le_div_iff₀ hpos]
  exact hreal

/-- **Norm bound from an almost-everywhere oscillation bound.** Let `p ≠ 0`, let `μ` be a nonzero
measure, and let `u` have finite `Lᵖ(μ)` seminorm. If `dist c (u y) ≤ A` for almost every `y`,
then `‖c‖ ≤ A + ‖u‖_{Lᵖ(μ)} / μ(X)^{1/p}`. -/
theorem norm_le_add_toReal_eLpNorm_div_of_ae_dist_le (hp : p ≠ 0) (h0 : μ ≠ 0)
    {u : X → F} (hu : eLpNorm u p μ ≠ ∞) {c : F} {A : ℝ} (h : ∀ᵐ y ∂μ, dist c (u y) ≤ A) :
    ‖c‖ ≤ A + (eLpNorm u p μ).toReal / (μ Set.univ).toReal ^ (1 / p.toReal) := by
  have hbound : ∀ᵐ y ∂μ, ‖c‖ - A ≤ ‖u y‖ :=
    h.mono fun y hy => by
      rw [dist_eq_norm] at hy
      linarith [norm_sub_norm_le c (u y)]
  linarith [le_toReal_eLpNorm_div_of_ae_le hp h0 hu hbound]

end MeasureTheory

namespace Complex

open MeasureTheory

/-- **Averaging over a planar disc.** If `p ≠ 0`, `u` has finite `Lᵖ(B(x, r))` seminorm and
`t ≤ ‖u y‖` for almost every `y ∈ B(x, r)`, then `t ≤ r^{-2/p} ‖u‖_{Lᵖ(B(x, r))}`, as the
area of `B(x, r)` is at least `r ^ 2`. -/
theorem le_rpow_neg_mul_toReal_eLpNorm_restrict_ball_of_ae_le {F : Type*} [SeminormedAddCommGroup F]
    {p : ℝ≥0∞} (hp : p ≠ 0) {u : ℂ → F} {x : ℂ} {r t : ℝ} (hr : 0 < r)
    (hu : eLpNorm u p (volume.restrict (ball x r)) ≠ ∞)
    (h : ∀ᵐ y ∂volume.restrict (ball x r), t ≤ ‖u y‖) :
    t ≤ r ^ (-(2 / p.toReal)) * (eLpNorm u p (volume.restrict (ball x r))).toReal := by
  have havg := le_toReal_eLpNorm_div_of_ae_le hp
    (fun h => (measure_ball_pos volume x hr).ne' (Measure.restrict_eq_zero.1 h)) hu h
  rw [Measure.restrict_apply_univ] at havg
  set s : ℝ := 1 / p.toReal
  have hVs : r ^ (2 * s) ≤ (volume (ball x r)).toReal ^ s := by
    rw [Real.rpow_mul hr.le, Complex.volume_ball]
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr.le,
      ENNReal.coe_toReal, NNReal.coe_real_pi, Real.rpow_two]
    nlinarith [Real.two_le_pi, sq_nonneg r]
  have hexp : r ^ (-(2 / p.toReal)) = (r ^ (2 * s))⁻¹ := by
    rw [← Real.rpow_neg hr.le]
    congr 1
    simp only [s]
    ring
  calc t ≤ (eLpNorm u p (volume.restrict (ball x r))).toReal / (volume (ball x r)).toReal ^ s :=
        havg
    _ ≤ (eLpNorm u p (volume.restrict (ball x r))).toReal / r ^ (2 * s) := by gcongr
    _ = _ := by rw [hexp, div_eq_mul_inv, mul_comm]

end Complex
