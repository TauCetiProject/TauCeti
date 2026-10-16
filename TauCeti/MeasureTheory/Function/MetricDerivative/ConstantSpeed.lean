/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ConstantSpeed
public import TauCeti.MeasureTheory.Function.MetricDerivative.Variation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Constant speed and metric derivatives

Mathlib's `HasConstantSpeedOnWith` specifies the variation on every subinterval. This file
identifies that condition with absolute continuity and an almost everywhere constant metric
derivative. In particular, unit-speed arclength curves have metric derivative one almost
everywhere, and their difference quotients converge to one there. Singleton intervals and
speed zero are included.

For finite-dimensional real normed targets, the norm of the usual derivative equals the
specified speed almost everywhere. No differentiability of a metric-valued curve is assumed.

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
  have hlength : eVariationOn γ (uIcc a b) =
      (l : ℝ≥0∞) * ENNReal.ofReal |b - a| := by
    have h := hγ (x := min a b) (y := max a b)
      (by simp [uIcc]) (by simp [uIcc])
    simpa [uIcc, max_sub_min_eq_abs] using h
  have hint : (∫⁻ t in uIcc a b, TauCeti.metricDerivative γ t) =
      ∫⁻ _ in uIcc a b, (l : ℝ≥0∞) := by
    rw [hrestrict, ← hAC.eVariationOn_eq_lintegral_metricDerivative,
      hlength]
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
