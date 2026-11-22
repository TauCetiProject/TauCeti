/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import TauCeti.NumberTheory.LSeries.Lerch.Integral

import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Nonpositive
import TauCeti.NumberTheory.LSeries.Lerch.Differential

/-!
# Comparisons between the Lerch transcendent and integer-weight polylogarithms

This module connects `TauCeti.lerchSeries` and `TauCeti.lerchIntegral` at `c = 1` with the
principal integer-weight polylogarithm `TauCeti.Polylog.polylog`.

## Main declarations

* `TauCeti.polylog_one_eq_mul_lerchSeries`: `Li_1(z) = z * Φ(z, 1, 1)` on `‖z‖ < 1`.
* `TauCeti.polylog_neg_nat_eq_mul_lerchSeries`: `Li_{-m}(z) = z * Φ(z, -m, 1)` on `‖z‖ < 1`
  for every `m : ℕ`.
* `TauCeti.mul_lerchIntegral_one_one_eq_polylog_one`: `z * lerchIntegral (1, z, 1) = Li_1(z)`
  across the cut plane `1 - z ∈ Complex.slitPlane`.

## References

* A. Erdélyi, W. Magnus, F. Oberhettinger, and F. G. Tricomi, *Higher Transcendental Functions*,
  Vol. 1, McGraw-Hill, 1953, Chapter 1.11.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  arXiv:1506.06161, (1.8)–(1.9).
-/

public section

open Filter Metric Set Topology

namespace TauCeti

/-- On the open unit disc `‖z‖ < 1`, `Li_1(z) = z * Φ(z, 1, 1)`. -/
theorem polylog_one_eq_mul_lerchSeries {z : ℂ} (hz : ‖z‖ < 1) :
    Polylog.polylog 1 z = z * lerchSeries z 1 1 := by
  refine (Polylog.hasSum_polylog_one hz).unique ?_
  convert (hasSum_lerchSeries hz 1 1).mul_left z using 2 with k
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [neg_one_mul, Complex.exp_neg, Complex.exp_log hk, pow_succ', div_eq_mul_inv, mul_assoc]

/-- On the open unit disc `‖z‖ < 1`, `Li_{-m}(z) = z * Φ(z, -m, 1)` for every `m : ℕ`. -/
theorem polylog_neg_nat_eq_mul_lerchSeries (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Polylog.polylog (-(m : ℤ)) z = z * lerchSeries z (-(m : ℂ)) 1 := by
  rw [Polylog.polylog_neg_nat_eq_div,
    lerchSeries_neg_nat_eq_div m hz fun n => by exact_mod_cast Nat.succ_ne_zero n,
    shiftedEulerianPolynomial_one_eval_eq_aeval, mul_div_assoc]

/-- Across the cut plane `1 - z ∈ Complex.slitPlane`, `z * lerchIntegral (1, z, 1) = Li_1(z)`. -/
theorem mul_lerchIntegral_one_one_eq_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * lerchIntegral (1, z, 1) = Polylog.polylog 1 z := by
  let Ω : Set ℂ := {w : ℂ | 1 - w ∈ Complex.slitPlane}
  have han1 : AnalyticOnNhd ℂ (fun w : ℂ => w * lerchIntegral (1, w, 1)) Ω := fun w hw =>
    analyticAt_id.mul (analyticOnNhd_lerchIntegral_middle one_pos one_pos w hw)
  have hev : (fun w : ℂ => w * lerchIntegral (1, w, 1)) =ᶠ[𝓝 (0 : ℂ)] Polylog.polylog 1 := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    rw [lerchIntegral_eq_lerchSeries one_pos hw1 one_pos, polylog_one_eq_mul_lerchSeries hw1]
  exact han1.eqOn_of_preconnected_of_eventuallyEq (Polylog.analyticOnNhd_polylog 1)
    Complex.isPreconnected_setOf_one_sub_mem_slitPlane (by simp [Ω]) hev hz

end TauCeti
