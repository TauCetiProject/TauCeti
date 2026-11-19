/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.Proximity.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
import TauCeti.Analysis.Meromorphic.Basic

/-!
# Cartan's single-circle integral presentation of the proximity function

Mathlib proves Cartan's iterated circle-average formula for `ValueDistribution.proximity f ⊤ R`
under a global `Meromorphic f` hypothesis on `ℂ`. However, for a fixed radius `R`, `proximity f ⊤ R`
depends only on the values of `f` along `sphere 0 |R|`. Functions meromorphic only on a disc (such
as the unit disc `ball 0 1`, where unit-circle singularities may prevent any global meromorphic
extension) still satisfy `MeromorphicOn f (sphere 0 |R|)` on every interior circle.

This file localizes Cartan's product-integrability and iterated circle-average theorems to a single
circle `sphere 0 |R|` (for single-circle arithmetic, translation, and reciprocal properties of
`ValueDistribution.proximity`, see `TauCeti.Analysis.Complex.ValueDistribution.Proximity.Basic`):

* `MeromorphicOn.integrableOn_log_norm_circleMap_sub`: product integrability of the Cartan kernel
  `(α, β) ↦ Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖` on `(0, 2π] × (0, 2π]`.
* `MeromorphicOn.circleIntegrable_circleAverage_log_norm_sub`: circle integrability of
  `a ↦ circleAverage (Real.log ‖f · - a‖) 0 R` on the unit circle.
* `MeromorphicOn.circleAverage_circleAverage_eq_proximity_top`: for `f : ℂ → ℂ` meromorphic on
  `sphere 0 |R|`,
  `circleAverage (fun a ↦ circleAverage (Real.log ‖f · - a‖) 0 R) 0 1 = proximity f ⊤ R`.

## Implementation notes

The product-integrability and Fubini arguments localize
`ValueDistribution.Cartan.integrableOn_cartanKernel`,
`ValueDistribution.circleIntegrable_circleAverage_log_norm_sub`, and
`ValueDistribution.circleAverage_circleAverage_eq_proximity_top` in
`Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation` (by Matteo Cipollina and
Stefan Kebekus) from global `Meromorphic f` to `MeromorphicOn f (sphere 0 |R|)`. Because
`ValueDistribution.Cartan.cartanKernel` in Mathlib is unexposed in a `public section` without an
unfolding lemma, we state the public integrability theorem directly for the uncurried kernel.

## References

* F. Calegari, V. Dimitrov, Y. Tang, *The unbounded denominators conjecture*, J. Amer. Math. Soc.
  **38** (2025), 627–702, §6.1.
* S. Lang, *Introduction to Complex Hyperbolic Spaces*, Springer, 1987, §VI.2.
-/

public section

open Filter MeasureTheory Metric Real Set

namespace MeromorphicOn

variable {f : ℂ → ℂ} {R : ℝ}

/-- Private local alias for the Cartan kernel `log ‖f (circleMap 0 R β) - circleMap 0 1 α‖`
(`ValueDistribution.Cartan.cartanKernel` in Mathlib is unexposed in a `public section`). -/
private noncomputable def localCartanKernel (f : ℂ → ℂ) (R α β : ℝ) : ℝ :=
  Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖

private lemma integrableOn_localCartanKernel_left (f : ℂ → ℂ) (R β : ℝ) :
    IntegrableOn (localCartanKernel f R · β) (Ioc 0 (2 * π)) := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1
  have h : CircleIntegrable (fun z ↦ Real.log ‖z - f (circleMap 0 R β)‖) 0 1 := by fun_prop
  simpa [localCartanKernel, norm_sub_rev, CircleIntegrable] using h

private lemma measurable_localCartanKernel (hf : MeromorphicOn f (sphere 0 |R|)) :
    Measurable (fun p : ℝ × ℝ ↦ localCartanKernel f R p.1 p.2) := by
  have hf_circle : Measurable (fun β : ℝ ↦ f (circleMap 0 R β)) :=
    hf.measurable_comp (continuous_circleMap 0 R).measurable (circleMap_mem_sphere' 0 R)
  exact Real.measurable_log.comp
    (((hf_circle.comp measurable_snd).sub
      ((continuous_circleMap 0 1).measurable.comp measurable_fst)).norm)

/-- Formula for the angular `L¹` norm of a slice of the Cartan kernel. Adapted from
`Mathlib.Analysis.Complex.ValueDistribution.Proximity.IntegralPresentation` (Matteo Cipollina and
Stefan Kebekus). -/
private lemma integral_norm_localCartanKernel_eq (f : ℂ → ℂ) (R β : ℝ) :
    ∫ α in Ioc 0 (2 * π), ‖localCartanKernel f R α β‖ =
      2 * (∫ α, (localCartanKernel f R α β)⁺
            ∂(volume.restrict (Ioc 0 (2 * π)))) -
        (2 * π) * log⁺ ‖f (circleMap 0 R β)‖ := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  calc ∫ α, ‖localCartanKernel f R α β‖ ∂μ
    _ = 2 * (∫ α, (localCartanKernel f R α β)⁺ ∂μ) -
          ∫ α, localCartanKernel f R α β ∂μ :=
      integral_abs_eq_two_mul_integral_posPart_sub_integral
        (integrableOn_localCartanKernel_left f R β)
    _ = 2 * (∫ α, (localCartanKernel f R α β)⁺ ∂μ) -
          2 * π * log⁺ ‖f (circleMap 0 R β)‖ := by
      congr
      set z := f (circleMap 0 R β)
      suffices h_avg : circleAverage (Real.log ‖z - ·‖) 0 1 = log⁺ ‖z‖ by
        convert congr(2 * π * $h_avg)
        simp [circleAverage_def, field, localCartanKernel,
          intervalIntegral.integral_of_le two_pi_pos.le]
      simp [norm_sub_rev]

/-- If `f` is meromorphic on `sphere 0 |R|`, then the Cartan kernel
`(α, β) ↦ log ‖f (circleMap 0 R β) - circleMap 0 1 α‖` is integrable on `(0, 2π] × (0, 2π]`.
Localizes `ValueDistribution.Cartan.integrableOn_cartanKernel` (Matteo Cipollina and Stefan Kebekus)
from global `Meromorphic f` to `MeromorphicOn f (sphere 0 |R|)`. -/
theorem integrableOn_log_norm_circleMap_sub (hf : MeromorphicOn f (sphere 0 |R|)) :
    IntegrableOn
      (Function.uncurry fun α β ↦ Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖)
      (uIoc 0 (2 * π) ×ˢ uIoc 0 (2 * π)) := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (2 * π))
  have hK_meas : Measurable (fun p : ℝ × ℝ ↦ localCartanKernel f R p.1 p.2) :=
    hf.measurable_localCartanKernel
  have hK_pos_meas :
      Measurable (fun p : ℝ × ℝ ↦ (localCartanKernel f R p.1 p.2)⁺) :=
    (_root_.continuous_posPart.measurable).comp hK_meas
  have h_int_posLog : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖) μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le).1 hf.circleIntegrable_posLog_norm
  have h_int_bound : Integrable (fun β ↦ log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2) μ :=
    h_int_posLog.add (integrable_const _)
  have h_int_pos :
      Integrable (fun β ↦ ∫ α, (localCartanKernel f R α β)⁺ ∂μ) μ := by
    refine Integrable.mono (h_int_bound.const_mul (2 * π))
      hK_pos_meas.stronglyMeasurable.integral_prod_left'.aestronglyMeasurable ?_
    filter_upwards with β
    have h_nonneg : 0 ≤ ∫ α, (localCartanKernel f R α β)⁺ ∂μ := by positivity
    have h_b_nonneg : 0 ≤ (2 * π) * (log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2) := by
      positivity [posLog_nonneg (x := ‖f (circleMap 0 R β)‖)]
    rw [Real.norm_of_nonneg h_nonneg, Real.norm_of_nonneg h_b_nonneg]
    have hle : ∫ α, (localCartanKernel f R α β)⁺ ∂μ ≤
        ∫ _, log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2 ∂μ := by
      refine integral_mono_of_nonneg (.of_forall (by simp [posPart])) (integrable_const _)
        (.of_forall fun α ↦ ?_)
      calc (localCartanKernel f R α β)⁺
        _ = log⁺ ‖f (circleMap 0 R β) + (-circleMap 0 1 α)‖ := by
          simp [localCartanKernel, posLog_def, posPart, max_comm, sub_eq_add_neg]
        _ ≤ log⁺ ‖f (circleMap 0 R β)‖ + log⁺ ‖-circleMap 0 1 α‖ + Real.log 2 :=
          posLog_norm_add_le (f (circleMap 0 R β)) (-circleMap 0 1 α)
        _ = log⁺ ‖f (circleMap 0 R β)‖ + Real.log 2 := by
          simp [norm_circleMap_zero, add_comm]
    simp [μ, Real.volume_real_Ioc_of_le two_pi_pos.le] at hle
    linarith
  have h_slice :
      Integrable (fun β ↦ ∫ α, ‖localCartanKernel f R α β‖ ∂μ) μ :=
    Integrable.congr ((h_int_pos.const_mul 2).sub (h_int_posLog.const_mul (2 * π)))
      (Eventually.of_forall fun β ↦ (integral_norm_localCartanKernel_eq f R β).symm)
  rw [Function.uncurry_def, uIoc_of_le two_pi_pos.le, IntegrableOn, Measure.volume_eq_prod,
    ← Measure.prod_restrict]
  simpa only [localCartanKernel] using (integrable_prod_iff' hK_meas.aestronglyMeasurable).2
    ⟨Eventually.of_forall (integrableOn_localCartanKernel_left f R), h_slice⟩

/-- Local version of `ValueDistribution.circleIntegrable_circleAverage_log_norm_sub`: if `f` is
meromorphic on `sphere 0 |R|`, then `a ↦ circleAverage (Real.log ‖f · - a‖) 0 R` is circle
integrable on the unit circle. -/
theorem circleIntegrable_circleAverage_log_norm_sub (hf : MeromorphicOn f (sphere 0 |R|)) :
    CircleIntegrable (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 := by
  have h_int := hf.integrableOn_log_norm_circleMap_sub
  rw [uIoc_of_le two_pi_pos.le, IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    at h_int
  have h_right :
      IntegrableOn
        (fun α ↦ ∫ β in 0..2 * π, Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖)
        (Ioc 0 (2 * π)) := by
    simpa [IntegrableOn, Function.uncurry, intervalIntegral.integral_of_le two_pi_pos.le] using
      h_int.integral_prod_left
  rw [CircleIntegrable, intervalIntegrable_iff_integrableOn_Ioc_of_le two_pi_pos.le]
  exact IntegrableOn.congr_fun (h_right.const_mul (2 * π)⁻¹)
    (fun _ _ ↦ by simp [circleAverage]) measurableSet_Ioc

/-- Local version of `ValueDistribution.circleAverage_circleAverage_eq_proximity_top`: if `f` is
meromorphic on `sphere 0 |R|`, then the unit-circle average over `a` of
`circleAverage (Real.log ‖f · - a‖) 0 R` equals `ValueDistribution.proximity f ⊤ R`. -/
theorem circleAverage_circleAverage_eq_proximity_top (hf : MeromorphicOn f (sphere 0 |R|)) :
    circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1 =
      ValueDistribution.proximity f ⊤ R := by
  let F : ℝ → ℝ → ℝ := fun α β ↦ Real.log ‖f (circleMap 0 R β) - circleMap 0 1 α‖
  calc circleAverage (fun a ↦ circleAverage (fun z ↦ Real.log ‖f z - a‖) 0 R) 0 1
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ α in 0..2 * π, ∫ β in 0..2 * π, F α β := by
      simp [circleAverage, F, mul_assoc]
    _ = (2 * π)⁻¹ * (2 * π)⁻¹ * ∫ β in 0..2 * π, ∫ α in 0..2 * π, F α β := by
      rw [MeasureTheory.intervalIntegral_intervalIntegral_swap
        hf.integrableOn_log_norm_circleMap_sub]
    _ = (2 * π)⁻¹ * ∫ β in 0..2 * π, ((2 * π)⁻¹ * ∫ α in 0..2 * π, F α β) := by
      simp [mul_comm, mul_left_comm, mul_assoc]
    _ = (2 * π)⁻¹ * ∫ β in 0..2 * π, log⁺ ‖f (circleMap 0 R β)‖ := by
      congr 1
      refine intervalIntegral.integral_congr fun β _ ↦ ?_
      calc (2 * π)⁻¹ * ∫ α in 0..2 * π, F α β
        _ = circleAverage (Real.log ‖f (circleMap 0 R β) - ·‖) 0 1 := by
          simp [F, circleAverage]
        _ = log⁺ ‖f (circleMap 0 R β)‖ := by
          simp [norm_sub_rev]
    _ = ValueDistribution.proximity f ⊤ R := by
      simp [ValueDistribution.proximity_top, circleAverage,
        intervalIntegral.integral_of_le two_pi_pos.le]

end MeromorphicOn
