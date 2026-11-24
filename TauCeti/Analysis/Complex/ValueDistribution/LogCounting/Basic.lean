/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Bounds for logarithmic counting weights and increments

Nevanlinna's logarithmic counting function weights a divisor `D` on a closed ball `closedBall 0 r`
by the radial logarithmic factors `(D z : ℝ) * Real.log (r * ‖z‖⁻¹)`. In
`Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic` (by Stefan Kebekus), nonnegativity of
these summands is proved inline for restrictions `toClosedBall r D` of whole-space divisors under
`1 ≤ r`.

This file provides the standalone pointwise nonnegativity lemma
`Function.locallyFinsuppWithin.mul_log_nonneg_of_subset_closedBall` for any nonnegative
`D : Function.locallyFinsuppWithin U ℤ` supported in `U ⊆ Metric.closedBall 0 r` over a seminormed
additive commutative group, with no `1 ≤ r`, `ProperSpace`, or global-support assumption.

The finite-subset estimate `sum_mul_log_le_logCounting_sub` bounds multiplicity-weighted mass
in a ball by the increment of the logarithmic counting function between two positive radii.
It applies on any proper normed additive commutative group, allows points at the origin and
radii below one, and includes equal radii. Keeping the increment accounts for the origin's
logarithmic contribution even when the individual counting values are negative.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math. Soc.
  **38** (2025), 627–702, §6.1.1.
* S. Lang, *Introduction to Complex Hyperbolic Spaces*, Springer, 1987, §VI.1.
* Matteo Cipollina, PNT+,
  `PrimeNumberTheoremAnd/Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Growth.lean`,
  for the punctured-ball comparison at twice the radius.
-/

public section

namespace Function.locallyFinsuppWithin

/-- Each radial logarithmic weight `(D z : ℝ) * Real.log (r * ‖z‖⁻¹)` is nonnegative for a
nonnegative `locallyFinsuppWithin` supported inside `Metric.closedBall 0 r` (when `‖z‖ = 0`,
`Real.log 0 = 0`, and outside `U`, `D z = 0`). -/
theorem mul_log_nonneg_of_subset_closedBall {E : Type*} [SeminormedAddCommGroup E]
    {U : Set E} {r : ℝ} {D : locallyFinsuppWithin U ℤ}
    (hU : U ⊆ Metric.closedBall 0 r) (hD : 0 ≤ D) (z : E) :
    0 ≤ (D z : ℝ) * Real.log (r * ‖z‖⁻¹) := by
  by_cases hz0 : ‖z‖ = 0
  · simp [hz0]
  by_cases hzu : z ∈ U
  · refine mul_nonneg (Int.cast_nonneg (hD z)) (Real.log_nonneg ?_)
    rw [← div_eq_mul_inv, one_le_div ((norm_nonneg z).lt_of_ne' hz0)]
    exact mem_closedBall_zero_iff.1 (hU hzu)
  · simp [apply_eq_zero_of_notMem _ hzu]

/-- The multiplicity-weighted mass of a finite subset of the closed ball of positive radius `r`,
weighted by `log (R / r)`, is bounded by the increment of `logCounting` from `r` to `R`.
The subset may contain the origin, and the radii may lie below one or coincide. Only divisor
values in the outer closed ball are assumed nonnegative. -/
theorem sum_mul_log_le_logCounting_sub {E : Type*} [NormedAddCommGroup E] [ProperSpace E]
    {D : locallyFinsupp E ℤ} {r R : ℝ} (hD : ∀ z, ‖z‖ ≤ R → 0 ≤ D z)
    (hr : 0 < r) (hrR : r ≤ R)
    (s : Finset E) (hs : ∀ z ∈ s, ‖z‖ ≤ r) :
    (∑ z ∈ s, (D z : ℝ)) * Real.log (R / r) ≤ D.logCounting R - D.logCounting r := by
  classical
  have hR : 0 < R := hr.trans_le hrR
  have hpos (z : E) (hz : ‖z‖ ≤ R) : D⁺ z = D z := by
    simpa only [posPart_apply] using posPart_eq_self.mpr (hD z hz)
  have hlog (t : ℝ) (ht : 0 < t) (htR : t ≤ R) : (D⁺).logCounting t = D.logCounting t := by
    have hball : toClosedBall t D⁺ = toClosedBall t D := by
      ext z
      by_cases hz : z ∈ Metric.closedBall (0 : E) |t|
      · rw [toClosedBall_eval_within _ hz, toClosedBall_eval_within _ hz]
        apply hpos z
        have hz' : ‖z‖ ≤ t := by
          simpa only [Metric.mem_closedBall, dist_zero_right, abs_of_pos ht] using hz
        exact hz'.trans htR
      · simp [apply_eq_zero_of_notMem _ hz]
    simp only [logCounting, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [hball, hpos 0 (by simpa only [norm_zero] using hR.le)]
  let K : locallyFinsupp E ℤ := ∑ z ∈ s, single z (D z)
  have hKD : K ≤ D⁺ := by
    intro z
    simp only [K, coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
    by_cases hz : z ∈ s
    · simpa only [hz, ite_true, posPart_apply] using le_posPart (D z)
    · simpa only [hz, ite_false, posPart_apply] using posPart_nonneg (D z)
  have hK (t : ℝ) (ht : r ≤ t) :
      K.logCounting t = ∑ z ∈ s, (D z : ℝ) * (Real.log t - Real.log ‖z‖) := by
    simp only [K, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun z hz ↦
      logCounting_single_eq_log_sub_const ((hs z hz).trans ht)
  have hmono : (D⁺ - K).logCounting r ≤ (D⁺ - K).logCounting R :=
    logCounting_mono (sub_nonneg.mpr hKD) hr hR hrR
  simp only [map_sub, Pi.sub_apply, hlog r hr hrR, hlog R hR le_rfl] at hmono
  calc
    (∑ z ∈ s, (D z : ℝ)) * Real.log (R / r) = K.logCounting R - K.logCounting r := by
      rw [hK R hrR, hK r le_rfl, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun z _ ↦ ?_
      rw [Real.log_div (ne_of_gt (hr.trans_le hrR)) hr.ne']
      ring
    _ ≤ D.logCounting R - D.logCounting r := by linarith

end Function.locallyFinsuppWithin
