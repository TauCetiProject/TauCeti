/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.PosLog
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Circle averages of `log⁺ ‖f‖⁻¹` and a Fatou bound

For `f` meromorphic on a circle, `log⁺ ‖f‖⁻¹ = log⁺ ‖f‖ - log ‖f‖` is circle integrable, and its
circle average is the difference of the circle averages of `log⁺ ‖f‖` and of `log ‖f‖`. This is the
identity `ValueDistribution.proximity_sub_proximity_inv_eq_circleAverage` of Nevanlinna theory, for
a function meromorphic only on the circle and a circle with arbitrary centre. Since the integrand is
nonnegative, the same identity also computes the lower Lebesgue integral of `log⁺ ‖f‖⁻¹` over one
period. Fatou's lemma then bounds the measure of angles where values on a sequence of circles
approach zero through nonzero values; this last result only needs circle integrability.

## Main results

* `MeromorphicOn.circleIntegrable_posLog_inv_norm` — `log⁺ ‖f‖⁻¹` is circle integrable.
* `MeromorphicOn.circleAverage_posLog_inv_norm` — the circle average of `log⁺ ‖f‖⁻¹` is the
  difference of the circle averages of `log⁺ ‖f‖` and of `log ‖f‖`.
* `MeromorphicOn.lintegral_ofReal_posLog_inv_norm_circleMap` — the lower Lebesgue integral of
  `log⁺ ‖f‖⁻¹` over one period of the circle is `2π` times that difference.
* `TauCeti.volume_setOf_tendsto_circleMap_nhdsNE_zero` — bounded circle averages of
  `log⁺ ‖f‖⁻¹` force the angles with nonzero radial values tending to zero to be null.
-/

public section

open MeasureTheory Metric Set Real

variable {f : ℂ → ℂ} {c : ℂ} {r : ℝ}

/-- `log⁺ ‖f‖⁻¹ = log⁺ ‖f‖ - log ‖f‖`, as functions. -/
private lemma posLog_inv_norm_eq_sub (f : ℂ → ℂ) :
    (fun z ↦ log⁺ ‖f z‖⁻¹) = (fun z ↦ log⁺ ‖f z‖) - fun z ↦ Real.log ‖f z‖ := by
  funext z
  simp only [Pi.sub_apply]
  linarith [posLog_sub_posLog_inv (x := ‖f z‖)]

namespace MeromorphicOn

/-- If `f` is meromorphic on a circle, then `log⁺ ‖f‖⁻¹` is circle integrable there. -/
theorem circleIntegrable_posLog_inv_norm (hf : MeromorphicOn f (sphere c |r|)) :
    CircleIntegrable (fun z ↦ log⁺ ‖f z‖⁻¹) c r := by
  rw [posLog_inv_norm_eq_sub]
  exact hf.circleIntegrable_posLog_norm.sub hf.circleIntegrable_log_norm

/-- If `f` is meromorphic on a circle, then the circle average of `log⁺ ‖f‖⁻¹` is the difference
of the circle averages of `log⁺ ‖f‖` and of `log ‖f‖`. -/
theorem circleAverage_posLog_inv_norm (hf : MeromorphicOn f (sphere c |r|)) :
    circleAverage (fun z ↦ log⁺ ‖f z‖⁻¹) c r =
      circleAverage (fun z ↦ log⁺ ‖f z‖) c r - circleAverage (fun z ↦ Real.log ‖f z‖) c r := by
  rw [posLog_inv_norm_eq_sub,
    circleAverage_sub hf.circleIntegrable_posLog_norm hf.circleIntegrable_log_norm]

/-- If `f` is meromorphic on a circle, then the lower Lebesgue integral of `log⁺ ‖f‖⁻¹` over one
period `(0, 2π]` of the circle is `2π` times the difference of the circle averages of `log⁺ ‖f‖`
and of `log ‖f‖`. -/
theorem lintegral_ofReal_posLog_inv_norm_circleMap (hf : MeromorphicOn f (sphere c |r|)) :
    ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (log⁺ ‖f (circleMap c r θ)‖⁻¹) =
      ENNReal.ofReal (2 * π * (circleAverage (fun z ↦ log⁺ ‖f z‖) c r -
        circleAverage (fun z ↦ Real.log ‖f z‖) c r)) := by
  have hlintegral : ∫⁻ θ in Ioc 0 (2 * π), ENNReal.ofReal (log⁺ ‖f (circleMap c r θ)‖⁻¹) =
      ENNReal.ofReal (∫ θ in 0..2 * π, log⁺ ‖f (circleMap c r θ)‖⁻¹) := by
    rw [intervalIntegral.integral_of_le two_pi_pos.le, ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1
        hf.circleIntegrable_posLog_inv_norm)
      (Filter.Eventually.of_forall fun θ ↦ posLog_nonneg)]
  rw [hlintegral, ← hf.circleAverage_posLog_inv_norm, circleAverage_def, smul_eq_mul]
  congr 1
  field_simp

end MeromorphicOn

namespace TauCeti

open Filter Topology
open scoped ENNReal

/-- **Fatou's lemma on circles.** If `log⁺ ‖f‖⁻¹` is integrable on the circles about `c` of
radii `ρ n`, and its circle averages there are at most `B`, then the angles in one period along
which `f (circleMap c (ρ n) θ)` tends to `0` through nonzero values form a null set. -/
theorem volume_setOf_tendsto_circleMap_nhdsNE_zero {ρ : ℕ → ℝ} {B : ℝ}
    (hf : ∀ n, CircleIntegrable (fun z ↦ log⁺ ‖f z‖⁻¹) c (ρ n))
    (hB : ∀ n, circleAverage (fun z ↦ log⁺ ‖f z‖⁻¹) c (ρ n) ≤ B) :
    volume {θ ∈ Ioc 0 (2 * π) | Tendsto (fun n ↦ f (circleMap c (ρ n) θ))
      atTop (𝓝[≠] 0)} = 0 := by
  set G : ℕ → ℝ → ℝ≥0∞ := fun n θ ↦ ENNReal.ofReal (log⁺ ‖f (circleMap c (ρ n) θ)‖⁻¹)
  have hG : ∀ n, AEMeasurable (G n) (volume.restrict (Ioc 0 (2 * π))) := fun n ↦
    (((intervalIntegrable_iff_integrableOn_Ioc_of_le
      two_pi_pos.le).1 (hf n)).aemeasurable).ennreal_ofReal
  have hbound : ∀ n, ∫⁻ θ in Ioc 0 (2 * π), G n θ ≤ ENNReal.ofReal (2 * π * B) := fun n ↦ by
    have hi := ofReal_integral_eq_lintegral_ofReal
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 (hf n))
      (Filter.Eventually.of_forall fun θ ↦ posLog_nonneg)
    rw [← hi, ← intervalIntegral.integral_of_le two_pi_pos.le]
    have haverage : ∫ θ in 0..2 * π, log⁺ ‖f (circleMap c (ρ n) θ)‖⁻¹ =
        2 * π * circleAverage (fun z ↦ log⁺ ‖f z‖⁻¹) c (ρ n) := by
      rw [circleAverage_def, smul_eq_mul]
      field_simp
    exact ENNReal.ofReal_le_ofReal (haverage ▸
      mul_le_mul_of_nonneg_left (hB n) two_pi_pos.le)
  refine measure_mono_null ?_ (measure_eq_top_of_setLIntegral_ne_top
    (AEMeasurable.liminf hG) (((lintegral_liminf_le' hG).trans
      (liminf_le_of_frequently_le' (.of_forall hbound))).trans_lt ENNReal.ofReal_lt_top).ne)
  refine fun θ hθ ↦ ⟨hθ.1, ?_⟩
  exact (ENNReal.tendsto_ofReal_atTop.comp (tendsto_atTop_mono
    (fun _ ↦ by rw [posLog_apply]; exact le_max_right _ _) (tendsto_log_atTop.comp
      (tendsto_inv_nhdsGT_zero.comp (tendsto_norm_nhdsNE_zero.comp hθ.2))))).liminf_eq

end TauCeti
