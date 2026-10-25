/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ConstantSpeed
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
public import TauCeti.Topology.MetricSpace.Arclength.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Constant speed and metric derivatives

Mathlib's `HasConstantSpeedOnWith` specifies the variation on every subinterval. This file
identifies that condition with absolute continuity and an almost everywhere constant metric
derivative. In particular, unit-speed arclength curves have metric derivative one almost
everywhere, and their difference quotients converge to one there. Singleton intervals and
speed zero are included. The natural parameterization of a continuous curve of bounded
variation is absolutely continuous on its length interval
(`BoundedVariationOn.absolutelyContinuousOnInterval_naturalParameterization`).

For finite-dimensional real normed targets, the norm of the usual derivative equals the
specified speed almost everywhere. No differentiability of a metric-valued curve is assumed.

This gives the **constant-speed energy identity**: along a curve of constant speed on `[a, b]`,
`(b - a) ∫ₐᵇ ‖γ'‖² = L²`, where `L` is the length of the curve
(`HasConstantSpeedOnWith.mul_integral_norm_deriv_sq`). For an arbitrary absolutely continuous
curve with square-integrable derivative the left side is at least `L²`
(`AbsolutelyContinuousOnInterval.eVariationOn_toReal_sq_le_mul_integral_norm_deriv_sq`), with
equality exactly for constant speed
(`AbsolutelyContinuousOnInterval.mul_integral_norm_deriv_sq_eq_eVariationOn_toReal_sq_iff`).
Thus, among absolutely continuous curves of a given length on a fixed interval, exactly the
constant-speed ones have least energy, and bounds proved through energy turn into length bounds
for them without loss.

The main inputs are Mathlib's constant-speed predicate and the metric fundamental theorem
and variation identity in `TauCeti.MeasureTheory.Function.MetricDerivative.Variation`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §1.1.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal Interval

variable {X : Type*} [PseudoMetricSpace X] {γ : ℝ → X} {a b : ℝ} {l : ℝ≥0}

/-- A curve of constant speed `l` on `[a, b]` has length `l |b - a|` there, in either order of
the endpoints. -/
theorem HasConstantSpeedOnWith.eVariationOn_uIcc (hγ : HasConstantSpeedOnWith γ (uIcc a b) l) :
    eVariationOn γ (uIcc a b) = ENNReal.ofReal (l * |b - a|) := by
  simpa [uIcc, max_sub_min_eq_abs] using hγ (x := min a b) (y := max a b)
    (by simp [uIcc]) (by simp [uIcc])

/-- A curve of constant variation speed has that metric derivative almost everywhere on its
parameter interval. This applies in particular to unit-speed arclength curves. -/
theorem HasConstantSpeedOnWith.ae_metricDerivative_eq
    (hγ : HasConstantSpeedOnWith γ (uIcc a b) l) :
    TauCeti.metricDerivative γ =ᵐ[volume.restrict (uIcc a b)] fun _ ↦ (l : ℝ≥0∞) := by
  have hAC := hγ.lipschitzOnWith.absolutelyContinuousOnInterval
  have hrestrict : volume.restrict (uIcc a b) = volume.restrict (uIoc a b) := by
    rw [uIcc, uIoc, restrict_Ioc_eq_restrict_Icc]
  have hle : TauCeti.metricDerivative γ ≤ᵐ[volume.restrict (uIcc a b)]
      fun _ ↦ (l : ℝ≥0∞) := by
    apply (ae_restrict_iff' measurableSet_uIcc).2
    filter_upwards [volume.ae_ne a, volume.ae_ne b] with t hta htb ht
    exact hγ.lipschitzOnWith.metricDerivative_le (TauCeti.uIcc_mem_nhds_of_ne ht hta htb)
  have hint : (∫⁻ t in uIcc a b, TauCeti.metricDerivative γ t) =
      ∫⁻ _ in uIcc a b, (l : ℝ≥0∞) := by
    rw [hrestrict, ← hAC.eVariationOn_eq_lintegral_metricDerivative, hγ.eVariationOn_uIcc,
      ENNReal.ofReal_mul l.coe_nonneg]
    simp [Real.volume_uIoc]
  apply ae_eq_of_ae_le_of_lintegral_le hle
  · rw [hrestrict]
    exact hAC.lintegral_metricDerivative_lt_top.ne
  · exact aemeasurable_const
  · exact hint.ge

/-- For an absolutely continuous curve, an almost everywhere constant metric derivative implies
constant variation speed on every subinterval. Absolute continuity is essential here. -/
theorem AbsolutelyContinuousOnInterval.hasConstantSpeedOnWith_of_ae_metricDerivative_eq
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hspeed : TauCeti.metricDerivative γ =ᵐ[volume.restrict (uIcc a b)]
      fun _ ↦ (l : ℝ≥0∞)) :
    HasConstantSpeedOnWith γ (uIcc a b) l := by
  rw [hasConstantSpeedOnWith_iff_ordered]
  intro x hx y hy hxy
  have hsub : Icc x y ⊆ uIcc a b := Icc_subset_uIcc.trans (uIcc_subset_uIcc hx hy)
  rw [inter_eq_right.mpr hsub]
  have hAC := hγ.mono (uIcc_subset_uIcc hx hy)
  rw [← uIcc_of_le hxy, hAC.eVariationOn_eq_lintegral_metricDerivative]
  have hae := hspeed.filter_mono
    (ae_mono (Measure.restrict_mono (uIoc_subset_uIcc.trans (uIcc_subset_uIcc hx hy)) le_rfl))
  rw [lintegral_congr_ae hae]
  simp [Real.volume_uIoc, abs_of_nonneg (sub_nonneg.mpr hxy)]

namespace TauCeti

/-- Constant variation speed is equivalent to absolute continuity with that metric derivative
almost everywhere. The statement includes zero speed and either order of the endpoints. -/
theorem hasConstantSpeedOnWith_iff_absolutelyContinuousOnInterval_metricDerivative_eq :
    HasConstantSpeedOnWith γ (uIcc a b) l ↔
      AbsolutelyContinuousOnInterval γ a b ∧
        metricDerivative γ =ᵐ[volume.restrict (uIcc a b)] fun _ ↦ (l : ℝ≥0∞) :=
  ⟨fun h ↦ ⟨h.lipschitzOnWith.absolutelyContinuousOnInterval, h.ae_metricDerivative_eq⟩,
    fun h ↦ h.1.hasConstantSpeedOnWith_of_ae_metricDerivative_eq h.2⟩

end TauCeti

/-- The natural parameterization of a continuous curve of bounded variation on `[a, b]` is
absolutely continuous on its length interval, because it has unit speed and is therefore
1-Lipschitz there. -/
theorem BoundedVariationOn.absolutelyContinuousOnInterval_naturalParameterization {X : Type*}
    [MetricSpace X] {γ : ℝ → X} (hγ : BoundedVariationOn γ (Icc a b))
    (hcont : ContinuousOn γ (Icc a b)) (hab : a ≤ b) :
    AbsolutelyContinuousOnInterval (naturalParameterization γ (Icc a b) a) 0
      (eVariationOn γ (Icc a b)).toReal := by
  refine LipschitzOnWith.absolutelyContinuousOnInterval (K := 1) ?_
  rw [uIcc_of_le ENNReal.toReal_nonneg, ← hγ.image_variationOnFromTo_Icc hcont hab]
  exact HasConstantSpeedOnWith.lipschitzOnWith
    (has_unit_speed_naturalParameterization γ hγ.locallyBoundedVariationOn (left_mem_Icc.2 hab))

/-- Along a curve of constant variation speed, the metric difference quotients converge to
the specified speed at almost every interior time. In particular, unit variation speed gives
a genuine metric-derivative limit of one. -/
theorem HasConstantSpeedOnWith.ae_tendsto_edist_div
    (hγ : HasConstantSpeedOnWith γ (uIcc a b) l) :
    ∀ᵐ t ∂volume.restrict (uIcc a b),
      Tendsto (fun s ↦ edist (γ s) (γ t) / edist s t) (𝓝[≠] t) (𝓝 (l : ℝ≥0∞)) := by
  have hAC := hγ.lipschitzOnWith.absolutelyContinuousOnInterval
  have hlim := (ae_restrict_iff' measurableSet_uIcc).2 hAC.ae_tendsto_metricDerivative
  filter_upwards [hlim, hγ.ae_metricDerivative_eq] with t ht heq
  rwa [heq] at ht

/-- In finite-dimensional real normed spaces a constant-speed curve is differentiable almost
everywhere, with derivative norm equal to its variation speed. -/
theorem HasConstantSpeedOnWith.ae_norm_deriv_eq {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [FiniteDimensional ℝ F] {γ : ℝ → F}
    (hγ : HasConstantSpeedOnWith γ (uIcc a b) l) :
    ∀ᵐ t ∂volume.restrict (uIcc a b), DifferentiableAt ℝ γ t ∧ ‖deriv γ t‖ = l := by
  have hAC := hγ.lipschitzOnWith.absolutelyContinuousOnInterval
  have hdiff := (ae_restrict_iff' measurableSet_uIcc).2
    hAC.boundedVariationOn.ae_differentiableAt_of_mem_uIcc
  filter_upwards [hdiff, hγ.ae_metricDerivative_eq] with t ht heq
  refine ⟨ht, ?_⟩
  rw [ht.hasDerivAt.metricDerivative_eq] at heq
  exact_mod_cast congrArg ENNReal.toReal heq

section Energy

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {γ : ℝ → F}

/-- The canonical derivative of a constant-speed curve is bounded by its speed almost everywhere,
so it lies in every `Lᵖ` space on the parameter interval. -/
theorem HasConstantSpeedOnWith.memLp_deriv (hγ : HasConstantSpeedOnWith γ (uIcc a b) l)
    (p : ℝ≥0∞) : MemLp (deriv γ) p (volume.restrict (uIoc a b)) := by
  have : IsFiniteMeasure (volume.restrict (uIoc a b)) := Real.isFiniteMeasure_restrict_Ioc _ _
  refine MemLp.of_bound (stronglyMeasurable_deriv γ).aestronglyMeasurable l ?_
  have h := (ae_restrict_iff' measurableSet_uIcc).1 hγ.ae_norm_deriv_eq
  refine (ae_restrict_iff' measurableSet_uIoc).2 ?_
  filter_upwards [h] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).2.le

/-- **The constant-speed energy identity.** Along a curve of constant speed `l` on `[a, b]`, the
`n`-th power of the speed integrates to `l ^ n (b - a)`. -/
theorem HasConstantSpeedOnWith.integral_norm_deriv_pow
    (hγ : HasConstantSpeedOnWith γ (uIcc a b) l) (n : ℕ) :
    ∫ t in a..b, ‖deriv γ t‖ ^ n = (l : ℝ) ^ n * (b - a) := by
  have h := (ae_restrict_iff' measurableSet_uIcc).1 hγ.ae_norm_deriv_eq
  rw [intervalIntegral.integral_congr_ae (g := fun _ ↦ (l : ℝ) ^ n),
    intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  filter_upwards [h] with t ht hmem
  rw [(ht (uIoc_subset_uIcc hmem)).2]

/-- Along a curve of constant speed on `[a, b]`, the energy `∫ₐᵇ ‖γ'‖²` multiplied by the length
`b - a` of the parameter interval is the square of the length of the curve. -/
theorem HasConstantSpeedOnWith.mul_integral_norm_deriv_sq
    (hγ : HasConstantSpeedOnWith γ (uIcc a b) l) :
    (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2 = (eVariationOn γ (uIcc a b)).toReal ^ 2 := by
  rw [hγ.integral_norm_deriv_pow, hγ.eVariationOn_uIcc,
    ENNReal.toReal_ofReal (mul_nonneg l.coe_nonneg (abs_nonneg _)), mul_pow, sq_abs]
  ring

namespace AbsolutelyContinuousOnInterval

/-- The energy of an absolutely continuous curve exceeds the length bound by `b - a` times the
`L²` deviation of the speed from its mean `(eVariationOn γ (uIcc a b)).toReal / (b - a)`. -/
private theorem mul_integral_norm_deriv_sq_sub_eVariationOn_toReal_sq
    (hγ : AbsolutelyContinuousOnInterval γ a b) (hab : a < b)
    (hL2 : MemLp (deriv γ) 2 (volume.restrict (uIoc a b))) :
    (b - a) * (∫ t in a..b, ‖deriv γ t‖ ^ 2) - (eVariationOn γ (uIcc a b)).toReal ^ 2 =
      (b - a) * ∫ t in a..b,
        (‖deriv γ t‖ - (eVariationOn γ (uIcc a b)).toReal / (b - a)) ^ 2 := by
  set L := (eVariationOn γ (uIcc a b)).toReal
  set m := L / (b - a)
  have hba : b - a ≠ 0 := (sub_pos.2 hab).ne'
  rw [uIoc_of_le hab.le] at hL2
  have hL1 : IntervalIntegrable (fun t ↦ ‖deriv γ t‖) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2
      (hL2.integrable one_le_two).norm
  have hsq : IntervalIntegrable (fun t ↦ ‖deriv γ t‖ ^ 2) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).2 hL2.integrable_norm_pow'
  have hlin : IntervalIntegrable (fun t ↦ 2 * m * ‖deriv γ t‖) volume a b :=
    hL1.const_mul _
  have hexp (t : ℝ) : (‖deriv γ t‖ - m) ^ 2 = ‖deriv γ t‖ ^ 2 - 2 * m * ‖deriv γ t‖ + m ^ 2 := by
    ring
  simp_rw [hexp]
  rw [intervalIntegral.integral_add (hsq.sub hlin) intervalIntegrable_const,
    intervalIntegral.integral_sub hsq hlin, intervalIntegral.integral_const_mul,
    hγ.integral_norm_deriv_eq_eVariationOn_toReal hab.le, intervalIntegral.integral_const,
    smul_eq_mul]
  simp only [m]
  field_simp
  ring

/-- **Energy bounds length.** For an absolutely continuous curve on `[a, b]` with
square-integrable derivative, the square of its length is at most `b - a` times its energy
`∫ₐᵇ ‖γ'‖²`. Both sides are symmetric in `a` and `b`. -/
theorem eVariationOn_toReal_sq_le_mul_integral_norm_deriv_sq
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hL2 : MemLp (deriv γ) 2 (volume.restrict (uIoc a b))) :
    (eVariationOn γ (uIcc a b)).toReal ^ 2 ≤ (b - a) * ∫ t in a..b, ‖deriv γ t‖ ^ 2 := by
  wlog hab : a ≤ b generalizing a b
  · have h := this hγ.symm (uIoc_comm a b ▸ hL2) (le_of_not_ge hab)
    rwa [uIcc_comm, intervalIntegral.integral_symm, mul_neg, ← neg_mul, neg_sub] at h
  rcases hab.eq_or_lt with rfl | hab
  · simp
  refine sub_nonneg.1 ?_
  rw [hγ.mul_integral_norm_deriv_sq_sub_eVariationOn_toReal_sq hab hL2]
  exact mul_nonneg (sub_pos.2 hab).le
    (intervalIntegral.integral_nonneg hab.le fun t _ ↦ sq_nonneg _)

/-- **Equality of energy and length.** For an absolutely continuous curve on `[a, b]` with
square-integrable derivative, `(b - a) ∫ₐᵇ ‖γ'‖²` equals the square of the length of the curve
exactly when the curve has constant speed on `[a, b]`. -/
theorem mul_integral_norm_deriv_sq_eq_eVariationOn_toReal_sq_iff
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hL2 : MemLp (deriv γ) 2 (volume.restrict (uIoc a b))) :
    (b - a) * (∫ t in a..b, ‖deriv γ t‖ ^ 2) = (eVariationOn γ (uIcc a b)).toReal ^ 2 ↔
      ∃ l : ℝ≥0, HasConstantSpeedOnWith γ (uIcc a b) l := by
  wlog hab : a ≤ b generalizing a b
  · have h := this hγ.symm (uIoc_comm a b ▸ hL2) (le_of_not_ge hab)
    rwa [uIcc_comm, intervalIntegral.integral_symm, mul_neg, ← neg_mul, neg_sub] at h
  rcases hab.eq_or_lt with rfl | hab
  · -- On a degenerate interval both sides hold, the right one with speed zero.
    simpa using ⟨0, hasConstantSpeedOnWith_zero_iff.2 (by simp)⟩
  refine ⟨fun h ↦ ?_, fun ⟨l, hl⟩ ↦ hl.mul_integral_norm_deriv_sq⟩
  set m := (eVariationOn γ (uIcc a b)).toReal / (b - a)
  have hm : 0 ≤ m := div_nonneg ENNReal.toReal_nonneg (sub_pos.2 hab).le
  have hdev := hγ.mul_integral_norm_deriv_sq_sub_eVariationOn_toReal_sq hab hL2
  rw [h, sub_self, eq_comm, mul_eq_zero, or_iff_right (sub_pos.2 hab).ne',
    intervalIntegral.integral_of_le hab.le] at hdev
  have hint : Integrable (fun t ↦ (‖deriv γ t‖ - m) ^ 2) (volume.restrict (Ioc a b)) := by
    rw [uIoc_of_le hab.le] at hL2
    exact (hL2.norm.sub (memLp_const m)).integrable_sq
  -- The speed is almost everywhere equal to its mean, so the metric derivative is constant.
  have hae := (integral_eq_zero_iff_of_nonneg (fun t ↦ sq_nonneg _) hint).1 hdev
  refine ⟨(⟨m, hm⟩ : ℝ≥0), hγ.hasConstantSpeedOnWith_of_ae_metricDerivative_eq ?_⟩
  have hrestrict : volume.restrict (uIcc a b) = volume.restrict (Ioc a b) := by
    rw [uIcc_of_le hab.le, restrict_Ioc_eq_restrict_Icc]
  rw [hrestrict]
  have hdiff' := (ae_restrict_iff' measurableSet_Ioc).2 <| by
    filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
    exact ht (uIcc_of_le hab.le ▸ Ioc_subset_Icc_self hmem)
  filter_upwards [hae, hdiff'] with t ht htd
  rw [htd.hasDerivAt.metricDerivative_eq]
  have : ‖deriv γ t‖ = m := by
    simpa [sub_eq_zero] using ht
  rw [← enorm_norm, this, Real.enorm_eq_ofReal hm]
  exact ENNReal.ofReal_eq_coe_nnreal hm

end AbsolutelyContinuousOnInterval

end Energy
