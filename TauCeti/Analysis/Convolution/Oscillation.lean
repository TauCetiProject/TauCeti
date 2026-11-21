/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Integral.Average

import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import TauCeti.Analysis.Convolution.Basic
import TauCeti.MeasureTheory.Integral.Average

/-!
# Convolution oscillation bounds on balls

Let `E` be a proper normed additive group with an additive Haar measure `μ`, and let `ρ : E → ℝ`
be a nonnegative kernel of integral `1`, supported in `ball 0 r` and bounded by
`C / μ.real (ball 0 r)`. For any Banach-valued function `f : E → F` integrable on `ball x r`, the
mollified value `(ρ ⋆ f) x` stays within `C` times the mean oscillation of `f` from the ball
average `⨍_{B(x, r)} f`:

`‖(ρ ⋆ f) x - ⨍_{B(x, r)} f‖ₑ ≤ C * ⨍⁻ z in B(x, r), ‖f z - ⨍_{B(x, r)} f‖ₑ`

(`TauCeti.enorm_convolution_sub_setAverage_ball_le`), and consequently the average distance from `f`
to the constant `(ρ ⋆ f) x` on `B(x, r)` is at most `1 + C` times the mean oscillation of `f` on
`B(x, r)` (`TauCeti.setLAverage_enorm_sub_convolution_le`).

## Main declarations

* `TauCeti.enorm_convolution_sub_setAverage_ball_le`: distance from `(ρ ⋆ f) x` to `⨍_{B(x, r)} f`.
* `TauCeti.setLAverage_enorm_sub_convolution_le`: mean deviation on `B(x, r)` from `(ρ ⋆ f) x`.

## References

* P. Hajłasz, *Sobolev mappings between manifolds and metric spaces*, in *Sobolev Spaces in
  Mathematics I*, Int. Math. Ser. (N.Y.) **8**, Springer (2009), 185–222, inequality (2.1).
* R. Schoen, K. Uhlenbeck, *Boundary regularity and the Dirichlet problem for harmonic maps*,
  J. Differential Geom. **18** (1983), 253–268, §4.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap MeasureTheory Metric
open scoped Convolution ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [ProperSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- **Distance from a mollification to the ball average.** Let `ρ ≥ 0` have integral `1`, support
in `ball 0 r`, and upper bound `C / μ.real (ball 0 r)`. For any `f` integrable on `ball x r`,
`‖(ρ ⋆ f) x - ⨍_{B(x, r)} f‖ₑ` is at most `C` times the mean oscillation of `f` on `ball x r`. -/
theorem enorm_convolution_sub_setAverage_ball_le {ρ : E → ℝ} {f : E → F} {x : E} {r C : ℝ}
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) (hρs : Function.support ρ ⊆ ball 0 r)
    (hρM : ∀ y, ρ y ≤ C / μ.real (ball 0 r)) (hf : IntegrableOn f (ball x r) μ) :
    ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - ⨍ z in ball x r, f z ∂μ‖ₑ ≤
      ENNReal.ofReal C * ⨍⁻ z in ball x r, ‖f z - ⨍ w in ball x r, f w ∂μ‖ₑ ∂μ := by
  obtain ⟨y, hy⟩ := exists_ne_zero_of_integral_ne_zero (by rw [hρ1]; exact one_ne_zero)
  have hr : 0 < r := Metric.nonempty_ball.1 ⟨y, hρs hy⟩
  have hBtop : μ (ball (0 : E) r) ≠ ∞ := measure_ball_lt_top.ne
  have hBreal_pos : 0 < μ.real (ball (0 : E) r) :=
    ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' hBtop
  set m : F := ⨍ z in ball x r, f z ∂μ
  have hρi : Integrable ρ μ := Integrable.of_integral_ne_zero (by rw [hρ1]; exact one_ne_zero)
  have hfi : Integrable ((ball x r).indicator f) μ := hf.integrable_indicator measurableSet_ball
  have hmem (t : E) : t ∈ ball (0 : E) r ↔ x - t ∈ ball x r := by simp [mem_ball, dist_eq_norm]
  -- Replace `f` by its indicator on `ball x r`, which does not change the convolution at `x`.
  have hconv_eq : (ρ ⋆[lsmul ℝ ℝ, μ] f) x = (ρ ⋆[lsmul ℝ ℝ, μ] (ball x r).indicator f) x :=
    (convolution_indicator_eq_of_forall_sub_mem (lsmul ℝ ℝ) fun t ht => (hmem t).1 (hρs ht)).symm
  have hconv_ex : ConvolutionExistsAt ρ ((ball x r).indicator f) x (lsmul ℝ ℝ) μ :=
    convolutionExists_of_ae_norm_le_of_integrable (lsmul ℝ ℝ) hρi.aestronglyMeasurable
      (.of_forall fun t => by rw [Real.norm_of_nonneg (hρ0 t)]; exact hρM t) hfi x
  rw [hconv_eq]
  refine (enorm_convolution_lsmul_sub_le hρ1 hconv_ex m).trans ?_
  calc ∫⁻ w, ‖ρ (x - w)‖ₑ * ‖(ball x r).indicator f w - m‖ₑ ∂μ
      ≤ ∫⁻ w, ENNReal.ofReal (C / μ.real (ball 0 r)) *
          (ball x r).indicator (fun w => ‖f w - m‖ₑ) w ∂μ := by
        refine lintegral_mono fun w => ?_
        by_cases hw : w ∈ ball x r
        · rw [Set.indicator_of_mem hw, Set.indicator_of_mem hw, ← ofReal_norm,
            Real.norm_of_nonneg (hρ0 _)]
          gcongr; exact hρM _
        · have h0 : ρ (x - w) = 0 := Function.notMem_support.1 fun h => hw <| by
            simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hρs h
          simp [h0]
    _ = ENNReal.ofReal (C / μ.real (ball 0 r)) * ∫⁻ z in ball x r, ‖f z - m‖ₑ ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_indicator measurableSet_ball]
    _ = ENNReal.ofReal C * ⨍⁻ z in ball x r, ‖f z - m‖ₑ ∂μ := by
        rw [ENNReal.ofReal_div_of_pos hBreal_pos, measureReal_def,
          ENNReal.ofReal_toReal hBtop, ← Measure.addHaar_ball_center μ x r,
          setLAverage_eq, div_eq_mul_inv, div_eq_mul_inv]
        ring

/-- **Mean deviation from a mollified value.** Under the hypotheses of
`TauCeti.enorm_convolution_sub_setAverage_ball_le`, the average distance on `ball x r` between `f`
and the constant `(ρ ⋆ f) x` is at most `1 + C` times the mean oscillation of `f` on `ball x r`. -/
theorem setLAverage_enorm_sub_convolution_le {ρ : E → ℝ} {f : E → F} {x : E} {r C : ℝ}
    (hρ0 : ∀ y, 0 ≤ ρ y) (hρ1 : ∫ y, ρ y ∂μ = 1) (hρs : Function.support ρ ⊆ ball 0 r)
    (hρM : ∀ y, ρ y ≤ C / μ.real (ball 0 r)) (hf : IntegrableOn f (ball x r) μ) :
    ⨍⁻ z in ball x r, ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ ≤
      ENNReal.ofReal (1 + C) * ⨍⁻ z in ball x r, ‖f z - ⨍ w in ball x r, f w ∂μ‖ₑ ∂μ := by
  obtain ⟨y, hy⟩ := exists_ne_zero_of_integral_ne_zero (by rw [hρ1]; exact one_ne_zero)
  have hr : 0 < r := Metric.nonempty_ball.1 ⟨y, hρs hy⟩
  have hB0 : μ (ball x r) ≠ 0 := (measure_ball_pos μ x hr).ne'
  have hBtop : μ (ball x r) ≠ ∞ := measure_ball_lt_top.ne
  have hC0 : 0 ≤ C := by
    by_contra hC
    have hneg : C / μ.real (ball (0 : E) r) < 0 :=
      div_neg_of_neg_of_pos (not_le.1 hC)
        (ENNReal.toReal_pos (measure_ball_pos μ 0 hr).ne' measure_ball_lt_top.ne)
    have h0 := (hρ0 0).trans (hρM 0)
    linarith
  set m : F := ⨍ w in ball x r, f w ∂μ
  set osc : ℝ≥0∞ := ⨍⁻ z in ball x r, ‖f z - m‖ₑ ∂μ
  have hpt (z : E) :
      ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ≤ ‖f z - m‖ₑ + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ := by
    calc ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ
        = ‖(f z - m) - ((ρ ⋆[lsmul ℝ ℝ, μ] f) x - m)‖ₑ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖f z - m‖ₑ + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ := eNorm_sub_le
  calc ⨍⁻ z in ball x r, ‖f z - (ρ ⋆[lsmul ℝ ℝ, μ] f) x‖ₑ ∂μ
      ≤ osc + ‖(ρ ⋆[lsmul ℝ ℝ, μ] f) x - m‖ₑ :=
        (setLAverage_mono_ae _ (.of_forall hpt)).trans_eq (setLAverage_add_const hB0 hBtop _ _)
    _ ≤ osc + ENNReal.ofReal C * osc :=
        add_le_add_right (enorm_convolution_sub_setAverage_ball_le hρ0 hρ1 hρs hρM hf) _
    _ = (1 + ENNReal.ofReal C) * osc := by rw [add_mul, one_mul]
    _ = ENNReal.ofReal (1 + C) * osc := by
        rw [ENNReal.ofReal_add zero_le_one hC0, ENNReal.ofReal_one]

end TauCeti

end
