/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Moments
public import TauCeti.MeasureTheory.Integral.Radial

/-!
# Quadratic moments of Yamabe bubbles

A quadratic form against the square of a radial bubble averages to its orthonormal trace
multiplied by the scalar second moment. This is the averaging step for quadratic scalar-curvature
Taylor terms in cutoff-bubble energies.

In dimension six the second moment diverges logarithmically. We give its exact truncated
quadratic integral and an explicit error bound: the leading term is
`8 |B(0,1)| tr(B) t⁴ log(1 + (R/t)²)`, and the error is at most
`8 |B(0,1)| |tr(B)| t⁴ H₃`. In particular the trace-free part contributes nothing, even before
taking a small-scale limit. The normalization is that of `TauCeti.Yamabe.bubble`.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), Section 6.
-/

public section

noncomputable section

open MeasureTheory Metric Module Real

namespace TauCeti.Yamabe

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} [Fintype ι]

/-- A quadratic form against the square of a bubble on a concentric ball is its orthonormal
trace divided by the dimension times the scalar second moment. -/
theorem setIntegral_ball_bilinear_self_mul_bubble_sq
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : 2 ≤ finrank ℝ E)
    (e : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) (a : E) (R : ℝ) :
    ∫ x in ball a R, B (x - a) (x - a) * bubble t a x ^ 2 ∂μ =
      ((∑ i, B (e i) (e i)) / (finrank ℝ E : ℝ)) *
        ∫ x in ball a R, ‖x - a‖ ^ 2 * bubble t a x ^ 2 ∂μ := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank ℝ E)
  simp_rw [bubble_sq hn ht.le]
  apply setIntegral_ball_bilinear_self_mul_radial μ e B a
    (w := fun r ↦ (2 * t / (t ^ 2 + r ^ 2)) ^ (finrank ℝ E - 2))
  exact ((continuous_const.div (continuous_const.add (continuous_id.pow 2))
    (fun r ↦ ne_of_gt (by positivity : 0 < t ^ 2 + r ^ 2))).pow _).continuousOn

/-- The exact logarithmic quadratic moment of a bubble square in dimension six. -/
theorem setIntegral_ball_bilinear_self_mul_bubble_sq_of_finrank_eq_six
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : finrank ℝ E = 6)
    (e : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) (a : E) {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in ball a R, B (x - a) (x - a) * bubble t a x ^ 2 ∂μ =
      8 * μ.real (ball (0 : E) 1) * (∑ i, B (e i) (e i)) * t ^ 4 *
        (log (1 + (R / t) ^ 2) - ∑ k ∈ Finset.range 3,
          (R ^ 2 / (t ^ 2 + R ^ 2)) ^ (k + 1) / (k + 1)) := by
  rw [setIntegral_ball_bilinear_self_mul_bubble_sq μ (by omega) e B ht a R]
  rw [setIntegral_ball_norm_sub_sq_mul_bubble_sq_of_finrank_eq_six μ hn ht hR a, hn]
  push_cast
  ring

/-- In dimension six the quadratic moment differs from its logarithmic leading term by an
explicit multiple of `t⁴`; there is no sign assumption on the trace. -/
theorem abs_setIntegral_ball_bilinear_self_mul_bubble_sq_sub_mul_log_le_of_finrank_eq_six
    (μ : Measure E) [μ.IsAddHaarMeasure] (hn : finrank ℝ E = 6)
    (e : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) (a : E) {R : ℝ} (hR : 0 ≤ R) :
    |∫ x in ball a R, B (x - a) (x - a) * bubble t a x ^ 2 ∂μ -
        8 * μ.real (ball (0 : E) 1) * (∑ i, B (e i) (e i)) * t ^ 4 *
          log (1 + (R / t) ^ 2)| ≤
      8 * μ.real (ball (0 : E) 1) * |∑ i, B (e i) (e i)| * t ^ 4 * harmonic 3 := by
  have h := abs_setIntegral_ball_norm_sub_sq_mul_bubble_sq_sub_mul_log_le_of_finrank_eq_six
    μ hn ht hR a
  calc
    _ = |(∑ i, B (e i) (e i)) / 6| *
        |(∫ x in ball a R, ‖x - a‖ ^ 2 * bubble t a x ^ 2 ∂μ) -
          48 * μ.real (ball (0 : E) 1) * t ^ 4 * log (1 + (R / t) ^ 2)| := by
      rw [setIntegral_ball_bilinear_self_mul_bubble_sq μ (by omega) e B ht a R, hn,
        ← abs_mul]
      congr 1
      push_cast
      ring
    _ ≤ |(∑ i, B (e i) (e i)) / 6| *
        (48 * μ.real (ball (0 : E) 1) * t ^ 4 * harmonic 3) :=
      mul_le_mul_of_nonneg_left h (abs_nonneg _)
    _ = _ := by rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 6)]; ring

end TauCeti.Yamabe
