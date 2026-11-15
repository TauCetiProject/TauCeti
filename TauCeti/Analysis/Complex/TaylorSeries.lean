/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Scalar power-series representations of holomorphic functions on discs

Mathlib's `Complex.hasSum_taylorSeries_on_eball` shows that the Taylor series around `c` of a
complex function `f : ℂ → ℂ` holomorphic on `Metric.eball c r` converges pointwise to `f`
throughout that open ball. By contrast, `DifferentiableOn.hasFPowerSeriesOnBall` constructs a
`HasFPowerSeriesOnBall` witness only on closed subdiscs of finite radius via a radius-dependent
Cauchy integral series, while `AnalyticOn.hasFPowerSeriesOnSubball` over `RCLike` requires
`r ≤ p.radius` as an input hypothesis (necessary over `ℝ`, where `1 / (1 + x ^ 2)` is real-analytic
on `ℝ` with Taylor radius `1`).

Over `ℂ`, Cauchy's theorem upgrades `r ≤ p.radius` from a hypothesis to a conclusion: on any open
extended-radius disc `Metric.eball c r` (`0 ≤ r ≤ ∞`), the canonical scalar Taylor series
`FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n f c / n!)` of a function holomorphic
on `Metric.eball c r` has radius of convergence at least `r`, and for `0 < r` represents `f` in the
sense of `HasFPowerSeriesOnBall` on the entire disc. Specializations are given for finite-radius
`Metric.ball c r` and for entire functions (`r = ⊤`).

## Main results

* `DifferentiableOn.le_radius_ofScalars`: if `f : ℂ → ℂ` is differentiable on `Metric.eball c r`,
  its scalar Taylor series around `c` has radius of convergence at least `r`.
* `DifferentiableOn.hasFPowerSeriesOnBall_ofScalars`: if `0 < r`, `f` has `HasFPowerSeriesOnBall`
  on `Metric.eball c r` with series
  `FormalMultilinearSeries.ofScalars ℂ (fun n ↦ iteratedDeriv n f c / n!)`.
* `DifferentiableOn.hasFPowerSeriesOnBall_ofScalars_of_ball`: the finite-radius version on
  `Metric.ball c r` (`0 < r`).
* `Differentiable.radius_ofScalars_eq_top`, `Differentiable.hasFPowerSeriesOnBall_ofScalars`: for
  an entire function `f : ℂ → ℂ`, the scalar Taylor series around any center `c : ℂ` has radius `⊤`
  and represents `f` on `Metric.eball c ⊤`.

## References

* Lars V. Ahlfors, *Complex Analysis*, 3rd ed., McGraw-Hill (1979), Chapter 4, §3.1 and
  Chapter 5, §1.2.
-/

public section

open Filter Topology
open scoped ENNReal NNReal Nat

/-- If `f : ℂ → ℂ` is holomorphic on `Metric.eball c r` (`0 ≤ r ≤ ∞`), its scalar Taylor series
around `c` has radius of convergence at least `r`. -/
theorem DifferentiableOn.le_radius_ofScalars {c : ℂ} {r : ℝ≥0∞} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.eball c r)) :
    r ≤ (FormalMultilinearSeries.ofScalars ℂ fun n ↦ iteratedDeriv n f c / (n ! : ℂ)).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun ρ hρ ↦ ?_
  have hmem : c + (ρ : ℂ) ∈ Metric.eball c r := by
    rw [Metric.mem_eball, eDist_eq_eNorm_sub, add_sub_cancel_left]
    simpa [eNorm_eq_nnNorm] using hρ
  have hsum := (Complex.hasSum_taylorSeries_on_eball hf hmem).summable.tendsto_atTop_zero.norm
  rw [norm_zero] at hsum
  refine FormalMultilinearSeries.le_radius_of_tendsto _ (l := 0) (hsum.congr fun n ↦ ?_)
  rw [FormalMultilinearSeries.ofScalars_norm]
  simp only [add_sub_cancel_left, smul_eq_mul, div_eq_mul_inv, norm_mul, norm_inv, norm_pow,
    Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
  ring

/-- A complex-valued function holomorphic on the open ball `Metric.eball c r` (`0 < r ≤ ∞`) is
represented on that ball by its scalar Taylor series around `c`. -/
theorem DifferentiableOn.hasFPowerSeriesOnBall_ofScalars {c : ℂ} {r : ℝ≥0∞} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.eball c r)) (hr : 0 < r) :
    HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ iteratedDeriv n f c / (n ! : ℂ)) c r where
  r_pos := hr
  r_le := hf.le_radius_ofScalars
  hasSum {y} hy := by
    have hmem : c + y ∈ Metric.eball c r := by
      rw [Metric.mem_eball, eDist_eq_eNorm_sub, add_sub_cancel_left]
      simpa [Metric.mem_eball, edist_zero_right] using hy
    refine (Complex.hasSum_taylorSeries_on_eball hf hmem).congr_fun fun n ↦ ?_
    rw [FormalMultilinearSeries.ofScalars_apply_eq]
    simp only [add_sub_cancel_left, smul_eq_mul, div_eq_mul_inv]
    ring

/-- A complex-valued function holomorphic on the finite open disc `Metric.ball c r` (`0 < r`) is
represented on that disc by its scalar Taylor series around `c`. -/
theorem DifferentiableOn.hasFPowerSeriesOnBall_ofScalars_of_ball {c : ℂ} {r : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball c r)) (hr : 0 < r) :
    HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ iteratedDeriv n f c / (n ! : ℂ))
      c (ENNReal.ofReal r) := by
  rw [← Metric.eball_ofReal] at hf
  exact hf.hasFPowerSeriesOnBall_ofScalars (ENNReal.ofReal_pos.mpr hr)

/-- For an entire function `f : ℂ → ℂ`, the scalar Taylor series around any center `c : ℂ` has
infinite radius of convergence. -/
theorem Differentiable.radius_ofScalars_eq_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) (c : ℂ) :
    (FormalMultilinearSeries.ofScalars ℂ fun n ↦ iteratedDeriv n f c / (n ! : ℂ)).radius = ⊤ :=
  top_unique hf.differentiableOn.le_radius_ofScalars

/-- An entire function `f : ℂ → ℂ` is represented on the whole complex plane (`r = ⊤`) around
every center `c : ℂ` by its scalar Taylor series around `c`. -/
theorem Differentiable.hasFPowerSeriesOnBall_ofScalars {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (c : ℂ) :
    HasFPowerSeriesOnBall f
      (FormalMultilinearSeries.ofScalars ℂ fun n ↦ iteratedDeriv n f c / (n ! : ℂ)) c ⊤ :=
  hf.differentiableOn.hasFPowerSeriesOnBall_ofScalars ENNReal.zero_lt_top
