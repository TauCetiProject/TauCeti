/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import TauCeti.Analysis.Complex.JensenFormula
import TauCeti.Analysis.Complex.Poisson.Logarithm
import TauCeti.MeasureTheory.Integral.PosLog

/-!
# The proximity function of a logarithmic derivative

Let `g` be holomorphic and zero-free on a neighbourhood of the closed disc `closedBall 0 R`. This
file bounds the Nevanlinna proximity function `m(r, g'/g) = proximity (logDeriv g) ⊤ r` on a
smaller circle `0 < r < R` in terms of `m(R, g)`, uniformly in `g`:

`m(r, g'/g) ≤ log⁺ ((m(R, g) / r) * R / (R - r)) + log 2 + exp (-1)` when `‖g 0‖ = 1`.

Estimates of this kind (lemmas on the logarithmic derivative) control `m(r, g'/g)` by the
characteristic of `g` with only a logarithmic loss, and are the analytic input to bounds on the
mean growth of covering maps of punctured planes.

The proof starts from the circle-mean bound `AnalyticOnNhd.circleAverage_norm_logDeriv_le`
(in `TauCeti.Analysis.Complex.Poisson.Logarithm`), obtained by differentiating the Herglotz
representation of `log g`:

`circleAverage ‖g'/g‖ c r ≤ 2 R / (R ^ 2 - r ^ 2) * circleAverage |log ‖g‖| c R`.

When `‖g 0‖ = 1`, the mean of `|log ‖g‖|` over `sphere 0 R` is `2 m(R, g)`
(`AnalyticOnNhd.circleAverage_abs_log_norm_of_ne_zero`), and the entropy estimate
`CircleIntegrable.circleAverage_posLog_le_posLog_circleAverage_add` converts the mean of `‖g'/g‖`
into a bound for the mean of `log⁺ ‖g'/g‖`.

## Main results

* `AnalyticOnNhd.proximity_logDeriv_top_le`: the zero-free logarithmic derivative estimate
  `m(r, g'/g) ≤ log⁺ ((m(R, g) / r) * R / (R - r)) + log 2 + exp (-1)` for `‖g 0‖ = 1` and
  `0 < r < R`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), 627–702, Lemma 6.1.7 and its proof (pp. 680–681), where the
  bound is stated with a strict inequality.
* W. K. Hayman, *Meromorphic Functions*, Oxford University Press (1964), §2.3.
-/

public section

open Complex Metric Real Set ValueDistribution

namespace AnalyticOnNhd

variable {g : ℂ → ℂ} {r R : ℝ}

/-- **The zero-free logarithmic derivative estimate.** If `g` is analytic and zero-free on a
neighbourhood of `closedBall 0 R` with `‖g 0‖ = 1` (for instance `g 0 = 1`), then for `0 < r < R`
the proximity function of `logDeriv g = deriv g / g` satisfies
`m(r, g'/g) ≤ log⁺ ((m(R, g) / r) * R / (R - r)) + log 2 + exp (-1)`. -/
theorem proximity_logDeriv_top_le (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hn : ∀ w ∈ closedBall 0 R, g w ≠ 0) (h0 : ‖g 0‖ = 1) (hr : 0 < r) (hrR : r < R) :
    proximity (logDeriv g) ⊤ r ≤
      log⁺ (proximity g ⊤ R / r * R / (R - r)) + Real.log 2 + Real.exp (-1) := by
  have hR : 0 < R := hr.trans hrR
  have hrR' : |r| < R := (abs_of_pos hr).trans_lt hrR
  set m := proximity g ⊤ R with hm_def
  have hm : 0 ≤ m := proximity_nonneg R
  -- The mean of `‖g'/g‖` over `sphere 0 r` is at most `2 R / (R ^ 2 - r ^ 2) * 2 m(R, g)`.
  have hmean : circleAverage (fun z ↦ ‖logDeriv g z‖) 0 r ≤ 2 * R / (R ^ 2 - r ^ 2) * (2 * m) := by
    have hg' : AnalyticOnNhd ℂ g (closedBall 0 |R|) := by rwa [abs_of_pos hR]
    have hn' : ∀ u ∈ closedBall (0 : ℂ) |R|, g u ≠ 0 := by rwa [abs_of_pos hR]
    have habs := hg'.circleAverage_abs_log_norm_of_ne_zero hn'
    rw [h0, Real.log_one, sub_zero] at habs
    calc circleAverage (fun z ↦ ‖logDeriv g z‖) 0 r
        ≤ 2 * R / (R ^ 2 - r ^ 2) * circleAverage (fun w ↦ |Real.log ‖g w‖|) 0 R :=
          hg.circleAverage_norm_logDeriv_le hn hrR'
      _ = 2 * R / (R ^ 2 - r ^ 2) * (2 * m) := by rw [habs, hm_def, proximity_top]
  -- That bound is at most twice `(m(R, g) / r) * R / (R - r)`, since `2 r ≤ R + r`.
  have hcmp : 2 * R / (R ^ 2 - r ^ 2) * (2 * m) ≤ 2 * (m / r * R / (R - r)) := by
    have hRr : 0 < R - r := sub_pos.2 hrR
    rw [sq_sub_sq R r, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    field_simp
    nlinarith [mul_nonneg (mul_nonneg hm hR.le) hRr.le]
  have hnonneg : 0 ≤ circleAverage (fun z ↦ ‖logDeriv g z‖) 0 r :=
    circleAverage_nonneg_of_nonneg fun _ _ ↦ norm_nonneg _
  calc proximity (logDeriv g) ⊤ r
      ≤ log⁺ (circleAverage (fun z ↦ ‖logDeriv g z‖) 0 r) + Real.exp (-1) := by
        rw [proximity_top]
        have hsub : sphere (0 : ℂ) |r| ⊆ closedBall 0 R :=
          sphere_subset_closedBall.trans (closedBall_subset_closedBall hrR'.le)
        exact ((hg.mono hsub).circleIntegrable_norm_logDeriv fun w hw ↦ hn w (hsub hw))
          |>.circleAverage_posLog_le_posLog_circleAverage_add fun _ _ ↦ norm_nonneg _
    _ ≤ log⁺ (2 * (m / r * R / (R - r))) + Real.exp (-1) := by
        gcongr
        · linarith
        · exact hmean.trans hcmp
    _ ≤ log⁺ 2 + log⁺ (m / r * R / (R - r)) + Real.exp (-1) := by
        gcongr
        exact posLog_mul
    _ = log⁺ (m / r * R / (R - r)) + Real.log 2 + Real.exp (-1) := by
        rw [posLog_eq_log (by norm_num)]
        ring

end AnalyticOnNhd
