/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

/-!
# Uniform convergence of convolutions with normalized bumps

Convolving a locally integrable function that is continuous at a point `x` with normalized bump
functions whose outer radii tend to zero converges to the function uniformly on a neighbourhood
filter of `x`. This upgrades Mathlib's joint convergence `ContDiffBump.convolution_tendsto_right`
to the form needed for the limit theorem of derivatives `hasFDerivAt_of_tendstoUniformlyOnFilter`.

## Main results

* `TauCeti.tendstoUniformlyOnFilter_convolution_normed`: the normalized-bump convolutions of a
  function continuous at `x` converge to it uniformly on a neighbourhood filter of `x`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped Convolution

variable {ι E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {mu : Measure E} [mu.IsAddHaarMeasure]

/-- Convolving a function that is continuous at `x` with normalized bumps of radius tending to zero
along a filter converges uniformly to it on a neighbourhood filter of `x`. -/
theorem tendstoUniformlyOnFilter_convolution_normed [CompleteSpace F] {x : E}
    {g : E → F}
    {l : Filter ι} (hgm : AEStronglyMeasurable g mu) (hgx : ContinuousAt g x)
    {phi : ι → ContDiffBump (0 : E)} (hphi : Tendsto (fun n => (phi n).rOut) l (𝓝 0)) :
    TendstoUniformlyOnFilter (fun n => g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, mu]
      (phi n).normed mu) g l (𝓝 x) := by
  have hconv : Tendsto (fun p : ι × E => (g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, mu]
      (phi p.1).normed mu) p.2) (l ×ˢ 𝓝 x) (𝓝 (g x)) := by
    simp only [convolution_flip]
    exact ContDiffBump.convolution_tendsto_right (hphi.comp tendsto_fst)
      (Eventually.of_forall fun _ => hgm) (hgx.tendsto.comp tendsto_snd) tendsto_snd
  have hdist : Tendsto (fun p : ι × E =>
      dist ((g ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).flip, mu] (phi p.1).normed mu) p.2) (g p.2))
      (l ×ˢ 𝓝 x) (𝓝 0) := by
    simpa only [dist_self, Function.comp_apply] using hconv.dist (hgx.tendsto.comp tendsto_snd)
  rw [Metric.tendstoUniformlyOnFilter_iff]
  intro ε hε
  simpa only [dist_comm] using (tendsto_order.1 hdist).2 ε hε

end TauCeti
