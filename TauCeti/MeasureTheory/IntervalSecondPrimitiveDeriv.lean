/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import TauCeti.MeasureTheory.IntervalWeakSecondDeriv
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Derivatives of the second primitive

The second primitive `K w` from `IntervalWeakSecondDeriv` is globally differentiable with
derivative the running integral of the density (differentiation under the integral against the
`1`-Lipschitz truncated kernel), and for a continuous density the running integral is in turn
differentiable within `[0,1]` with derivative the density itself (fundamental theorem of
calculus).

These two steps are the engine of the free-beam eigenfunction bootstrap: a weak eigenfunction
is an affine function plus a second primitive twice over, so it acquires a full fourth-order
derivative chain within `[0,1]` and the interval ODE classification applies.

The scalar field is an arbitrary `RCLike` `𝕜`.

## Main results

* `TauCeti.hasDerivAt_secondPrimitive`: `(K w)' = firstPrimitive w` everywhere.
* `TauCeti.hasDerivWithinAt_firstPrimitive_of_continuous`: `(firstPrimitive w)' = w` within
  `[0,1]` for continuous `w`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

variable {𝕜 : Type*} [RCLike 𝕜]

/-- Running integral of a density on the unit interval, cut off below the parameter. -/
def firstPrimitive (w : ℝ → 𝕜) (t : ℝ) : 𝕜 :=
  ∫ s, (Set.Iio t).indicator w s ∂unitIocMeasure

/-- The running integral depends only on the almost-everywhere class of the density. -/
theorem firstPrimitive_congr_ae {w w' : ℝ → 𝕜} (h : w =ᵐ[unitIocMeasure] w') :
    firstPrimitive w = firstPrimitive w' := by
  funext t
  refine integral_congr_ae ?_
  filter_upwards [h] with s hs
  by_cases hst : s ∈ Set.Iio t
  · rw [Set.indicator_of_mem hst, Set.indicator_of_mem hst, hs]
  · rw [Set.indicator_of_notMem hst, Set.indicator_of_notMem hst]

/-- **Differentiation under the integral**: the second primitive is everywhere
differentiable, with derivative the running integral of the density. -/
theorem hasDerivAt_secondPrimitive {w : ℝ → 𝕜} (hw : Integrable w unitIocMeasure)
    (t₀ : ℝ) : HasDerivAt (secondPrimitive w) (firstPrimitive w t₀) t₀ := by
  have hnull : unitIocMeasure {t₀} = 0 := unitIocMeasure_singleton t₀
  have hmeasF : ∀ t : ℝ, AEStronglyMeasurable
      (fun s => (secondPrimitiveKernel t s : 𝕜) * w s) unitIocMeasure := fun t =>
    ((RCLike.continuous_ofReal.comp
      (continuous_secondPrimitiveKernel.comp
        (Continuous.prodMk continuous_const continuous_id))).aestronglyMeasurable).mul
      hw.aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun t s => (secondPrimitiveKernel t s : 𝕜) * w s)
    (F' := fun s => (Set.Iio t₀).indicator w s)
    (bound := fun s => ‖w s‖)
    (μ := unitIocMeasure) (x₀ := t₀)
    (Filter.univ_mem)
    (Filter.Eventually.of_forall hmeasF)
    (integrable_secondPrimitiveKernel_mul hw t₀)
    (hw.aestronglyMeasurable.indicator measurableSet_Iio)
    ?_ hw.norm ?_
  · exact key.2
  · refine Filter.Eventually.of_forall fun s => ?_
    refine LipschitzOnWith.of_dist_le_mul fun t _ t' _ => ?_
    rw [dist_eq_norm, dist_eq_norm]
    have hdiff : (secondPrimitiveKernel t s : 𝕜) * w s
        - (secondPrimitiveKernel t' s : 𝕜) * w s
        = ((secondPrimitiveKernel t s - secondPrimitiveKernel t' s : ℝ) : 𝕜) * w s := by
      push_cast
      ring
    rw [hdiff, norm_mul, RCLike.norm_ofReal, Real.norm_eq_abs]
    have hcoe : ((Real.nnabs ‖w s‖ : ℝ≥0) : ℝ) = ‖w s‖ := by
      simp
    rw [hcoe]
    calc |secondPrimitiveKernel t s - secondPrimitiveKernel t' s| * ‖w s‖
        ≤ |t - t'| * ‖w s‖ :=
          mul_le_mul_of_nonneg_right (abs_secondPrimitiveKernel_sub_le t t' s)
            (norm_nonneg _)
      _ = ‖w s‖ * ‖t - t'‖ := by rw [Real.norm_eq_abs]; ring
  · have hae : ∀ᵐ s ∂unitIocMeasure, s ≠ t₀ := by
      rw [MeasureTheory.ae_iff]
      refine measure_mono_null (fun s hs => ?_) hnull
      simpa using hs
    filter_upwards [hae] with s hs
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · -- `s < t₀`: locally the kernel is `t - s`.
      have hlin : HasDerivAt (fun t : ℝ => ((t - s : ℝ) : 𝕜) * w s) ((1 : 𝕜) * w s) t₀ := by
        have h1 : HasDerivAt (fun t : ℝ => ((t - s : ℝ) : 𝕜)) 1 t₀ := by
          have hbase : HasDerivAt (fun t : ℝ => t - s) 1 t₀ :=
            (hasDerivAt_id t₀).sub_const s
          have hcomp := (RCLike.ofRealCLM (K := 𝕜)).hasDerivAt.scomp t₀ hbase
          simpa only [Function.comp_def, RCLike.ofRealCLM_apply, RCLike.ofReal_one,
            one_smul] using hcomp
        simpa using h1.mul_const (w s)
      have heq : (fun t : ℝ => ((t - s : ℝ) : 𝕜) * w s)
          =ᶠ[nhds t₀] fun t : ℝ => (secondPrimitiveKernel t s : 𝕜) * w s := by
        filter_upwards [eventually_gt_nhds hlt] with t ht
        rw [secondPrimitiveKernel_of_le ht.le]
      have hres := heq.hasDerivAt_iff.mp hlin
      rw [Set.indicator_of_mem (Set.mem_Iio.mpr hlt)]
      simpa using hres
    · -- `s > t₀`: locally the kernel vanishes.
      have hzero : HasDerivAt (fun _ : ℝ => (0 : 𝕜)) 0 t₀ := hasDerivAt_const _ _
      have heq : (fun _ : ℝ => (0 : 𝕜))
          =ᶠ[nhds t₀] fun t : ℝ => (secondPrimitiveKernel t s : 𝕜) * w s := by
        filter_upwards [eventually_lt_nhds hgt] with t ht
        rw [secondPrimitiveKernel_of_ge ht.le]
        simp
      have hres := heq.hasDerivAt_iff.mp hzero
      rw [Set.indicator_of_notMem (by simpa using hgt.le)]
      simpa using hres

/-- On the unit interval the running integral is the interval integral of the density. -/
theorem firstPrimitive_eq_intervalIntegral {w : ℝ → 𝕜}
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    firstPrimitive w t = ∫ s in (0 : ℝ)..t, w s := by
  have hset : Set.Ioc (0 : ℝ) 1 ∩ Set.Iio t = Set.Ioo 0 t := by
    ext s
    constructor
    · rintro ⟨⟨hs0, _⟩, hst⟩
      exact ⟨hs0, hst⟩
    · rintro ⟨hs0, hst⟩
      exact ⟨⟨hs0, le_trans (le_of_lt hst) ht.2⟩, hst⟩
  rw [firstPrimitive, unitIocMeasure_def, integral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, hset,
    intervalIntegral.integral_of_le ht.1, ← integral_Ioc_eq_integral_Ioo]

/-- **Fundamental theorem of calculus within the interval**: for a continuous density the
running integral is differentiable within `[0,1]` with derivative the density. -/
theorem hasDerivWithinAt_firstPrimitive_of_continuous {w : ℝ → 𝕜} (hw : Continuous w)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (firstPrimitive w) (w t₀) (Set.Icc 0 1) t₀ := by
  have hFTC : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, w x) (w t₀) t₀ :=
    intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable 0 t₀)
      (hw.stronglyMeasurableAtFilter _ _) hw.continuousAt
  refine (hFTC.hasDerivWithinAt).congr ?_ ?_
  · intro y hy
    exact firstPrimitive_eq_intervalIntegral hy
  · exact firstPrimitive_eq_intervalIntegral ht₀

end

end TauCeti
