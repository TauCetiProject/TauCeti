/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
public import TauCeti.NumberTheory.LSeries.Lerch.Integral

import Mathlib.Analysis.Analytic.Uniqueness
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy

/-!
# Comparisons between the Lerch transcendent and integer-weight polylogarithms

This module connects `TauCeti.lerchSeries` and `TauCeti.lerchIntegral` at `c = 1` with the
principal integer-weight polylogarithm `TauCeti.Polylog.polylog`.

## Main declarations

* `TauCeti.polylog_eq_mul_lerchSeries_one_right`: `Li_n(z) = z * Φ(z, n, 1)` on `‖z‖ < 1` for
  every `n : ℤ`.
* `TauCeti.mul_lerchIntegral_one_right_eq_polylog`: `z * lerchIntegral (m, z, 1) = Li_m(z)` across
  the cut plane `1 - z ∈ Complex.slitPlane` for every `m : ℤ` with `0 < m`.

## References

* A. Erdélyi, W. Magnus, F. Oberhettinger, and F. G. Tricomi, *Higher Transcendental Functions*,
  Vol. 1, McGraw-Hill, 1953, Chapter 1.11.
* J. C. Lagarias and W.-C. W. Li, *The Lerch zeta function III. Polylogarithms and special values*,
  arXiv:1506.06161, (1.8)–(1.9).
-/

public section

open Filter Metric Set Topology

namespace TauCeti

/-- On the open unit disc `‖z‖ < 1`, `Li_n(z) = z * Φ(z, n, 1)` for every integer weight
`n : ℤ`. -/
theorem polylog_eq_mul_lerchSeries_one_right (n : ℤ) {z : ℂ} (hz : ‖z‖ < 1) :
    Polylog.polylog n z = z * lerchSeries z n 1 := by
  refine (Polylog.hasSum_polylog n hz).unique ?_
  convert (hasSum_lerchSeries hz (n : ℂ) 1).mul_left z using 2 with k
  have hk : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  rw [mul_comm (-(n : ℂ)), ← Complex.cpow_def_of_ne_zero hk, Complex.cpow_neg,
    Complex.cpow_intCast, ← mul_assoc, ← pow_succ', ← div_eq_mul_inv]

/-- Across the cut plane `1 - z ∈ Complex.slitPlane`, `z * lerchIntegral (m, z, 1) = Li_m(z)`
for every positive integer weight `m : ℤ`. -/
theorem mul_lerchIntegral_one_right_eq_polylog (m : ℤ) (hm : 0 < m)
    {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * lerchIntegral (m, z, 1) = Polylog.polylog m z := by
  let Ω : Set ℂ := {w : ℂ | 1 - w ∈ Complex.slitPlane}
  have hm' : (0 : ℝ) < (m : ℂ).re := by simpa using hm
  have han1 : AnalyticOnNhd ℂ (fun w : ℂ => w * lerchIntegral (m, w, 1)) Ω := fun w hw =>
    analyticAt_id.mul (analyticOnNhd_lerchIntegral_middle hm' one_pos w hw)
  have hev : (fun w : ℂ => w * lerchIntegral (m, w, 1)) =ᶠ[𝓝 (0 : ℂ)] Polylog.polylog m := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self one_pos)] with w hw
    have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    rw [lerchIntegral_eq_lerchSeries hm' hw1 one_pos, polylog_eq_mul_lerchSeries_one_right m hw1]
  exact han1.eqOn_of_preconnected_of_eventuallyEq (Polylog.analyticOnNhd_polylog m)
    Complex.isPreconnected_setOf_one_sub_mem_slitPlane (by simp [Ω]) hev hz

end TauCeti
