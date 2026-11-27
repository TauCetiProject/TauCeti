/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Limits of convolutions at infinity

`MeasureTheory.tendsto_convolution_lsmul_atTop` gives the limit of the convolution of a
Lebesgue-integrable scalar kernel and an essentially bounded function with a limit at positive
infinity. The convolution acts by `ContinuousLinearMap.lsmul`, and a kernel of mass one
preserves the limit. This applies to fixed-bandwidth smoothing, such as the squared-sinc
smoothing of Delange's model.
-/

public section

open Filter
open scoped Convolution Topology

namespace MeasureTheory

/-- Convolving an essentially bounded function with an integrable scalar kernel preserves its
limit at positive infinity up to multiplication by the kernel's integral. -/
theorem tendsto_convolution_lsmul_atTop {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {K : ℝ → ℝ} {f : ℝ → E} {c : E} {M : ℝ}
    (hK : Integrable K) (hf : AEStronglyMeasurable f volume)
    (hM : ∀ᵐ t ∂volume, ‖f t‖ ≤ M) (hc : Tendsto f atTop (𝓝 c)) :
    Tendsto (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) atTop (𝓝 ((∫ t, K t) • c)) := by
  have hlim : ∀ t : ℝ, Tendsto (fun x : ℝ ↦ K t • f (x - t)) atTop (𝓝 (K t • c)) := by
    intro t
    have hshift : Tendsto (fun x : ℝ ↦ x - t) atTop atTop := by
      simpa only [id_eq, sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-t) tendsto_id
    exact (hc.comp hshift).const_smul (K t)
  have htranslate (x : ℝ) :=
    (volume.measurePreserving_sub_left x).quasiMeasurePreserving
  have hmeas (x : ℝ) : AEStronglyMeasurable (fun t : ℝ ↦ K t • f (x - t)) volume :=
    hK.aestronglyMeasurable.smul (hf.comp_quasiMeasurePreserving (htranslate x))
  have hbound (x : ℝ) : ∀ᵐ t ∂volume, ‖K t • f (x - t)‖ ≤ ‖K t‖ * M := by
    filter_upwards [(htranslate x).ae hM] with t ht
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left ht (norm_nonneg _)
  have h := tendsto_integral_filter_of_dominated_convergence (fun t ↦ ‖K t‖ * M)
    (.of_forall hmeas) (.of_forall hbound) (hK.norm.mul_const M) (.of_forall hlim)
  rw [integral_smul_const] at h
  exact h.congr fun x ↦ by simp only [convolution_def, ContinuousLinearMap.lsmul_apply]

end MeasureTheory
