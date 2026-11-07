/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.InteriorMorrey
public import TauCeti.Analysis.Sobolev.W1p.PreciseRepresentative
import TauCeti.Analysis.Sobolev.Mollification.Basic
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.Analysis.Calculus.MeanValue
import TauCeti.Analysis.Convex.Topology

/-!
# Sharp Lipschitz representatives on convex domains

The precise representative of a real `W^{1,∞}` function on a convex open set is Lipschitz
with constant at most the essential supremum of its weak gradient. In particular the
whole-space representative has this bound. Neither boundedness of the domain nor boundary
regularity is needed.

Local continuity comes from the interior Morrey theorem. Mollification on a neighborhood of
each segment gives the sharp constant, without assuming that smooth functions are dense in
the `W^{1,∞}` norm.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.8.2.
* G. Leoni, *A First Course in Sobolev Spaces*, Chapter 7.
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Metric Filter TauCeti.MeasureTheory
open scoped Topology Convolution ENNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}

private theorem W1p.memLp_indicator_preciseRepresentative (u : W1p μ Ω ∞) :
    MemLp ((Ω : Set E).indicator (preciseRepresentative μ (W1p.value u))) ∞ μ := by
  apply (memLp_indicator_iff_restrict Ω.isOpen.measurableSet.nullMeasurableSet).2
  exact (Lp.memLp (W1p.value u)).ae_eq (W1p.ae_eq_preciseRepresentative u)

private theorem W1p.norm_fderiv_convolution_indicator_le (u : W1p μ Ω ∞)
    (ρ : ContDiffBump (0 : E)) {z : E}
    (hz : ∀ y ∈ tsupport (ρ.normed μ), z - y ∈ Ω) :
    ‖fderiv ℝ (ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ]
      ((Ω : Set E).indicator (preciseRepresentative μ (W1p.value u)))) z‖ ≤
        ‖W1p.gradient u‖ := by
  let f := (Ω : Set E).indicator (preciseRepresentative μ (W1p.value u))
  let G := (Ω : Set E).indicator (fun x ↦ innerSL ℝ (W1p.gradient u x))
  have hf := W1p.memLp_indicator_preciseRepresentative u
  have hG₀ : MemLp (fun x ↦ innerSL ℝ (W1p.gradient u x)) ∞ (μ.restrict Ω) :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp_memLp' (Lp.memLp (W1p.gradient u))
  have hG : MemLp G ∞ μ := by
    exact (memLp_indicator_iff_restrict (f := fun x ↦ innerSL ℝ (W1p.gradient u x))
      Ω.isOpen.measurableSet.nullMeasurableSet).2 hG₀
  have hweak : HasWeakFDerivOn μ Ω f G := by
    exact ((W1p.hasWeakFDerivOn u).congr_ae (W1p.ae_eq_preciseRepresentative u)).indicator
  have hbound : ∀ᵐ x ∂μ, ‖G x‖ ≤ ‖W1p.gradient u‖ := by
    have h := (ae_restrict_iff' Ω.isOpen.measurableSet).1
      (Lp.ae_norm_le_norm_top (W1p.gradient u))
    filter_upwards [h] with x hx
    by_cases hxΩ : x ∈ Ω
    · simpa [G, hxΩ] using hx hxΩ
    · simp [G, hxΩ]
  rw [← convolution_flip, hweak.fderiv_convolution_right (hf.locallyIntegrable le_top)
    (hG.locallyIntegrable le_top) _ ρ.contDiff_normed ρ.hasCompactSupport_normed z hz,
    convolution_flip, convolution_def]
  calc
    ‖∫ y, ContinuousLinearMap.lsmul ℝ ℝ (ρ.normed μ y) (G (z - y)) ∂μ‖ ≤
        ∫ y, ρ.normed μ y * ‖W1p.gradient u‖ ∂μ := by
      apply norm_integral_le_of_norm_le (ρ.integrable_normed.mul_const _)
      filter_upwards [((μ.measurePreserving_sub_left z).quasiMeasurePreserving.ae hbound)]
        with y hy
      simpa only [ContinuousLinearMap.lsmul_apply, norm_smul,
        Real.norm_of_nonneg (ρ.nonneg_normed y)] using
          mul_le_mul_of_nonneg_left hy (ρ.nonneg_normed y)
    _ = ‖W1p.gradient u‖ := by rw [integral_mul_const, ρ.integral_normed, one_mul]

/-- On a convex open set the precise representative of a `W^{1,∞}` class is Lipschitz,
with the sharp bound given by the essential supremum of its weak gradient. -/
theorem W1p.lipschitzOnWith_preciseRepresentative_of_convex (u : W1p μ Ω ∞)
    (hΩ : Convex ℝ (Ω : Set E)) :
    LipschitzOnWith ‖W1p.gradient u‖₊ (preciseRepresentative μ (W1p.value u)) Ω := by
  let f := (Ω : Set E).indicator (preciseRepresentative μ (W1p.value u))
  have hf := W1p.memLp_indicator_preciseRepresentative u
  have hc := W1p.continuousOn_preciseRepresentative (ENNReal.natCast_lt_top _) u
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  obtain ⟨δ, hδ, hδΩ⟩ := (isCompact_segment ℝ x y).exists_cthickening_subset_open Ω.isOpen
    (hΩ.segment_subset hx hy)
  let ρ : ℕ → ContDiffBump (0 : E) := ContDiffBump.shrinking hδ
  have hsupp (n : ℕ) (z : E) (hz : z ∈ segment ℝ x y)
      (w : E) (hw : w ∈ tsupport ((ρ n).normed μ)) : z - w ∈ Ω := by
    apply hδΩ
    apply mem_cthickening_of_dist_le _ z δ _ hz
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
    rw [(ρ n).tsupport_normed_eq, mem_closedBall, dist_zero_right] at hw
    simp only [ρ, ContDiffBump.rOut_shrinking] at hw
    exact hw.trans (div_le_self hδ.le (by simp))
  have hlim (z : E) (hz : z ∈ Ω) :
      Tendsto (fun n ↦ ((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) z)
        atTop (𝓝 (preciseRepresentative μ (W1p.value u) z)) := by
    have hcont : ContinuousAt f z := by
      exact (hc.continuousAt (Ω.isOpen.mem_nhds hz)).congr
        (Filter.EventuallyEq.symm (Ω.isOpen.eventually_mem hz |>.mono fun t ht ↦
          indicator_of_mem ht _))
    simpa only [f, indicator_of_mem hz] using
      ContDiffBump.convolution_tendsto_right (ContDiffBump.tendsto_rOut_shrinking hδ)
        (Eventually.of_forall fun _ ↦ hf.aestronglyMeasurable)
        (hcont.tendsto.comp tendsto_snd) (tendsto_const_nhds (x := z))
  have hle (n : ℕ) :
      dist (((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) x)
        (((ρ n).normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] f) y) ≤
          ‖W1p.gradient u‖ * dist x y := by
    rw [dist_eq_norm, dist_eq_norm]
    apply (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
    · intro z _
      exact ((ρ n).hasCompactSupport_normed.contDiff_convolution_left
        (ContinuousLinearMap.lsmul ℝ ℝ) (ρ n).contDiff_normed
        (hf.locallyIntegrable le_top) (n := ⊤)).differentiable (by simp) z
    · intro z hz
      exact W1p.norm_fderiv_convolution_indicator_le u (ρ n) (hsupp n z hz)
    · exact right_mem_segment ℝ x y
    · exact left_mem_segment ℝ x y
  exact le_of_tendsto ((hlim x hx).dist (hlim y hy)) (Eventually.of_forall hle)

/-- On the whole space the precise representative of a `W^{1,∞}` class is globally
Lipschitz with constant at most the essential supremum of its weak gradient. -/
theorem W1p.lipschitzWith_preciseRepresentative (u : W1p μ ⊤ ∞) :
    LipschitzWith ‖W1p.gradient u‖₊ (preciseRepresentative μ (W1p.value u)) := by
  rw [← lipschitzOnWith_univ]
  exact W1p.lipschitzOnWith_preciseRepresentative_of_convex u convex_univ

end TauCeti
