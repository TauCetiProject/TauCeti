/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.McDiarmid.Independent

import TauCeti.Analysis.RCLike.Basic

/-!
# Bounded differences for complex-valued functions

Applying
`ProbabilityTheory.iIndepFun.measureReal_abs_sub_integral_ge_le_of_bounded_differences`
to the real and imaginary parts gives a tail bound for the norm of a centered complex statistic.
-/

public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory.iIndepFun

/-- McDiarmid's inequality for the norm of a centered statistic of independent coordinates.
If changing coordinate `i` moves the statistic by at most `c i`, the tail at `t ≥ 0` is at most
`4 exp (-t² / (2 ∑ i, (c i)²))`. When all coordinate bounds vanish, the displayed bound is
the trivial bound `4`. -/
theorem measureReal_norm_sub_integral_ge_le_of_bounded_differences
    {Ω ι 𝕜 : Type*} [MeasurableSpace Ω] [Fintype ι] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜] {β : ι → Type*} [∀ i, MeasurableSpace (β i)]
    {P : Measure Ω} {X : ∀ i, Ω → β i} (h : iIndepFun X P)
    (hX : ∀ i, AEMeasurable (X i) P) (f : (∀ i, β i) → 𝕜) (hf : Measurable f)
    (c : ι → ℝ≥0)
    (hbd : ∀ (i : ι) (x y : ∀ i, β i), (∀ j ≠ i, x j = y j) → ‖f x - f y‖ ≤ c i)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ ‖f (fun i ↦ X i ω) - ∫ w, f (fun i ↦ X i w) ∂P‖} ≤
      4 * Real.exp (-(t ^ 2) / (2 * ∑ i, (c i : ℝ) ^ 2)) := by
  have := h.isProbabilityMeasure
  let F (ω : Ω) := f (fun i ↦ X i ω)
  have hnorm := h.hasSubgaussianMGF_of_bounded_differences hX (fun x ↦ ‖f x‖) hf.norm c
    (fun i x y hxy ↦ (abs_norm_sub_norm_le _ _).trans (hbd i x y hxy))
  have hFm := (hf.comp_aemeasurable (aemeasurable_pi_iff.2 hX)).aestronglyMeasurable
  have hF : Integrable F P := (integrable_norm_iff hFm).mp
    ((hnorm.integrable.add (integrable_const (∫ w, ‖F w‖ ∂P))).congr
      (ae_of_all _ fun ω ↦ sub_add_cancel _ _))
  have ht_half : 0 ≤ t / 2 := by positivity
  have hre := h.measureReal_abs_sub_integral_ge_le_of_bounded_differences hX
    (fun x ↦ RCLike.re (f x)) (RCLike.continuous_re.measurable.comp hf) c (fun i x y hxy ↦ by
      simpa only [map_sub] using (RCLike.abs_re_le_norm (f x - f y)).trans (hbd i x y hxy))
    ht_half
  have him := h.measureReal_abs_sub_integral_ge_le_of_bounded_differences hX
    (fun x ↦ RCLike.im (f x)) (RCLike.continuous_im.measurable.comp hf) c (fun i x y hxy ↦ by
      simpa only [map_sub] using (RCLike.abs_im_le_norm (f x - f y)).trans (hbd i x y hxy))
    ht_half
  rw [integral_re hF] at hre
  rw [integral_im hF] at him
  let A := {ω | t / 2 ≤ |RCLike.re (F ω) - RCLike.re (∫ w, F w ∂P)|}
  let B := {ω | t / 2 ≤ |RCLike.im (F ω) - RCLike.im (∫ w, F w ∂P)|}
  have hsubset : {ω | t ≤ ‖F ω - ∫ w, F w ∂P‖} ⊆ A ∪ B := by
    intro ω hω
    have hnorm := (Set.mem_ofPred_eq.mp hω).trans
      (RCLike.norm_le_abs_re_add_abs_im (F ω - ∫ w, F w ∂P))
    simp only [A, B, Set.mem_union, Set.mem_ofPred_eq, map_sub] at *
    by_contra! h
    linarith [h.1, h.2]
  calc
    _ ≤ P.real A + P.real B :=
      (measureReal_mono hsubset (measure_ne_top _ _)).trans (measureReal_union_le _ _)
    _ ≤ _ := by
      convert add_le_add hre him using 1
      ring_nf

end ProbabilityTheory.iIndepFun
