/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# A constant bounded almost everywhere by a function in `Lᵖ`

If a real number `t` satisfies `t ≤ ‖u y‖` for almost every `y` with respect to a nonzero
measure `μ`, then taking `Lᵖ(μ)` seminorms of both sides gives `t ≤ μ(X)^{-1/p} ‖u‖_{Lᵖ(μ)}`
(`MeasureTheory.le_toReal_eLpNorm_div_of_ae_le`). Applied to a restricted measure `μ.restrict s`
and to `t - A`, this is the averaging step that turns a pointwise oscillation bound
`t ≤ ‖u y‖ + A` on `s` into a sup bound. In particular, a function `f` that is `L`-Lipschitz on a
ball `ball z r` of nonzero measure and agrees almost everywhere there with `g` satisfies
`‖f z‖ ≤ L * r + ‖g‖_{Lᵖ(ball z r)} / μ(ball z r)^{1/p}`
(`MeasureTheory.norm_le_of_lipschitzOnWith_ball`).

For a planar disc `B(x, r) ⊆ ℂ`, whose area `π r²` is at least `r²`, this reads
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

/-- **Pointwise bound from a Lipschitz bound on a ball.** Let `p ≠ 0`, let `f` be `L`-Lipschitz on
`ball z r` with `μ (ball z r) ≠ 0`, and let `g` agree with `f` almost everywhere on `ball z r`
with finite `Lᵖ` seminorm there. Then
`‖f z‖ ≤ L * r + ‖g‖_{Lᵖ(ball z r)} / μ(ball z r)^{1/p}`. -/
theorem norm_le_of_lipschitzOnWith_ball [PseudoMetricSpace X] [OpensMeasurableSpace X]
    {f g : X → F} {L : ℝ≥0} {z : X} {r : ℝ} (hμ : μ (ball z r) ≠ 0)
    (hf : LipschitzOnWith L f (ball z r)) (hfg : g =ᵐ[μ.restrict (ball z r)] f)
    (hp : p ≠ 0) (hg : eLpNorm g p (μ.restrict (ball z r)) ≠ ∞) :
    ‖f z‖ ≤ L * r + (eLpNorm g p (μ.restrict (ball z r))).toReal /
      (μ (ball z r)).toReal ^ (1 / p.toReal) := by
  have hr : 0 < r := by
    by_contra h
    exact hμ (by rw [ball_eq_empty.2 (not_lt.1 h), measure_empty])
  have hbound : ∀ᵐ y ∂μ.restrict (ball z r), ‖f z‖ - L * r ≤ ‖g y‖ := by
    filter_upwards [hfg, ae_restrict_mem measurableSet_ball] with y hy hyB
    rw [hy]
    have hd := hf.dist_le_mul z (mem_ball_self hr) y hyB
    have := mul_le_mul_of_nonneg_left (mem_ball'.1 hyB).le L.coe_nonneg
    rw [dist_eq_norm] at hd
    linarith [norm_sub_norm_le (f z) (f y)]
  have havg := le_toReal_eLpNorm_div_of_ae_le hp (Measure.restrict_eq_zero.not.2 hμ) hg hbound
  rw [Measure.restrict_apply_univ] at havg
  linarith

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
